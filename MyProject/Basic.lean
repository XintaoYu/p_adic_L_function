import Mathlib
set_option maxHeartbeats 10000000000000000

open BigOperators Nat


section p_adic_summable
variable (p:ℕ )[Fact (Nat.Prime p)]
--lim i → +OO     ||a i|| =0
variable {a : ℕ → ℚ_[p]}
lemma summable_in_p_adic_field (a:ℕ →ℚ_[p]): Summable a ↔ Filter.Tendsto (fun (x :ℕ ) => ‖a x‖) Filter.atTop
(nhds 0)  :=by
   constructor
   · intro ha
     rw[summable_iff_vanishing_norm]at ha
     rw[EMetric.tendsto_atTop]
     intro w sw
     have :w=⊤ ∨ ¬ w=⊤ :=by exact eq_or_ne w ⊤
     rcases this with g1|g2
     · use 0
       intro j
       rw[edist_eq_coe_nnnorm_sub]
       simp
       rw[g1]
       exact ENNReal.coe_lt_top
     · have jp0: w.toReal >0 :=by
        refine ENNReal.toReal_pos (Ne.symm (ne_of_lt sw)) g2
       have jp1: ∃ s, ∀ (t : Finset ℕ), Disjoint t s → ‖∑ i ∈ t, a i‖ < w.toReal :=by
        exact ha  w.toReal jp0
       rcases jp1 with ⟨s,ds⟩
       have jp2 :∃ N:ℕ ,∀ n>N , Disjoint {n} s :=by
        have jp01: ∃ n, s ⊆ Finset.range n :=by
          exact Finset.exists_nat_subset_range s
        rcases jp01 with ⟨n,hn⟩
        use n
        intro m hm
        have : Disjoint {m} (Finset.range n ) :=by
         refine Finset.disjoint_singleton_left.mpr ?_
         by_contra ds
         have j1: m<n :=by exact List.mem_range.mp ds
         have j2:¬ m<n :=by exact Nat.not_lt_of_gt hm
         exact j2 j1
        have: Disjoint {m} s :=by
         exact
          Disjoint.symm
          (Finset.disjoint_of_subset_left hn (id (Disjoint.symm this)))
        exact this
       rcases jp2 with ⟨N,dN⟩
       have jp21:∀ n ≥ (N+1),Disjoint {n} s :=by
        intro n dn
        have:n>N :=by exact dn
        exact dN n this
       use (N+1)
       intro n dn
       have jp3 : ‖∑ i ∈ {n}, a i‖ < w.toReal :=by
         have :Disjoint {n} s :=by exact jp21  n dn
         exact ds {n} this
       simp at jp3
       rw[edist_eq_coe_nnnorm_sub]
       simp
       have jp31:(‖a n‖.toNNReal:ENNReal) <ENNReal.ofReal (w.toReal):=by
        refine ENNReal.coe_lt_coe_of_lt ?_
        exact (Real.toNNReal_lt_toNNReal_iff jp0).mpr jp3
       have : ‖a n‖.toNNReal=‖a n‖₊ :=by exact norm_toNNReal
       rw[this] at jp31
       have: ENNReal.ofReal (w.toReal)=w :=by
         exact ENNReal.ofReal_toReal_eq_iff.mpr g2
       rw[this] at jp31
       exact jp31
   · intro ha
     rw[summable_iff_vanishing_norm]
     intro w hw
     have jp1:∃ n:ℕ ,∀ i>n ,‖a i‖ ≤  w /2:=by
       have: ∀ ε > 0, ∃ N, ∀ n ≥ N, edist ‖a n‖ 0 < ε:=by
         exact EMetric.tendsto_atTop.mp ha
       have :∃ N, ∀ n ≥ N, edist ‖a n‖ 0 <(w/2).toNNReal:=by
         have s1: (w/2).toNNReal>0 :=by
           refine Real.toNNReal_pos.mpr ?_
           exact half_pos hw
         have s2 :((w / 2).toNNReal:ENNReal) > 0:=by
           exact ENNReal.coe_pos.mpr s1
         exact this (w/2).toNNReal s2
       rcases this with ⟨n,hn⟩
       use n-1
       intro i si
       have ds1:i≥ n :=by exact Nat.le_of_pred_lt si
       have u1: edist ‖a i‖ 0 <(w/2).toNNReal :=by exact hn i ds1
       rw[edist_eq_coe_nnnorm_sub] at u1
       simp at u1
       have u2: ‖a i‖ <w / 2 :=by
         refine (Real.toNNReal_lt_toNNReal_iff_of_nonneg ?hr).mp ?_
         · exact norm_nonneg (a i)
         · have: ‖a i‖₊=‖a i‖.toNNReal :=by exact Eq.symm norm_toNNReal
           rw[←this]
           exact u1
       exact le_of_lt u2

     rcases jp1 with ⟨n1,hn1⟩
     use Finset.range (n1+1)
     intro t hst
     have jp2:∀ h ∈  t , h>n1 :=by
       intro h hs
       by_contra u1
       have : h≤ n1 :=by exact Nat.le_of_not_lt u1
       have : h <n1+1 :=by exact Order.lt_add_one_iff.mpr this
       have :  h∈ Finset.range (n1+1) :=by
         refine Finset.mem_range.mpr this
       have : ¬  Disjoint t (Finset.range (n1 + 1)) :=by
         refine Finset.not_disjoint_iff.mpr ?_
         use h
       exact this hst
     have jp3 :∀ h∈  t , ‖a h‖ ≤  w/2 :=by
       intro h hs
       exact hn1 h (jp2 h hs)
     rcases Finset.eq_empty_or_nonempty t with g1|g2
     · rw[g1]
       simp
       exact hw
     ·  have jp5: ‖∑ i ∈ t, a i‖ ≤  w/2 :=by refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty g2  jp3
        have jp6: w/2< w :=by exact div_two_lt_of_pos hw
        exact lt_of_le_of_lt jp5 jp6
end  p_adic_summable

section multichoose'

variable {p : ℕ} [Fact (Nat.Prime p)]

attribute [ext] PadicInt.ext

lemma l1(n:ℕ ):  Continuous (fun (x:ℤ_[p]) => Polynomial.eval (x:ℚ_[p])
(ascPochhammer ℚ_[p] n)):=by
  have: (fun (x:ℤ_[p]) => Polynomial.eval (x:ℚ_[p]) (ascPochhammer ℚ_[p] n))=
   (fun (y:ℚ_[p]) => Polynomial.eval y (ascPochhammer ℚ_[p] n))∘(fun (x:ℤ_[p]) =>
    (x:ℚ_[p])) :=by rfl
  rw[this]
  refine Continuous.comp (Polynomial.continuous_eval₂ (ascPochhammer ℚ_[p] n)
   (RingHom.id ℚ_[p])
   ) (continuous_iff_le_induced.mpr fun U a => a)

lemma l2(n:ℕ ): Continuous (fun (x:ℤ_[p]) =>  (Nat.factorial n )•
 Ring.multichoose (x:ℚ_[p]) n):=by
  have j1:∀ (x:ℤ_[p]), Nat.factorial n • Ring.multichoose (x:ℚ_[p]) n=
   Polynomial.eval (x:ℚ_[p]) (ascPochhammer ℚ_[p] n):=by
    intro x
    rw[Ring.factorial_nsmul_multichoose_eq_ascPochhammer]
    exact Polynomial.ascPochhammer_smeval_eq_eval (x:ℚ_[p]) n

  have j2: (fun (x:ℤ_[p]) =>  Nat.factorial n • Ring.multichoose (x:ℚ_[p]) n)=
  (fun (x:ℤ_[p]) => Polynomial.eval (x:ℚ_[p]) (ascPochhammer ℚ_[p] n)):=by
    exact
      (Set.eqOn_univ (fun (x:ℤ_[p]) => n.factorial • Ring.multichoose (x:ℚ_[p]) n)
        (fun (x:ℤ_[p]) =>
            Polynomial.eval (↑x) (ascPochhammer ℚ_[p] n))).mp
        fun ⦃x⦄ _ => j1 ↑x
  rw[j2]
  exact l1 n
lemma l3(n:ℕ ): Continuous (fun (x:ℤ_[p]) =>
Ring.multichoose (x:ℚ_[p]) n):=by
  have: ∀ (x:ℤ_[p]),Ring.multichoose (x:ℚ_[p]) n =  ((Nat.factorial n):ℚ)⁻¹•
  ( Nat.factorial n • Ring.multichoose (x:ℚ_[p]) n):=by
   intro x
   have: ((Nat.factorial n):ℚ)⁻¹•( Nat.factorial n • Ring.multichoose (x:ℚ_[p]) n)=
   (((Nat.factorial n):ℚ))⁻¹• Nat.factorial n•  Ring.multichoose (x:ℚ_[p]) n :=by
     exact rfl
   rw[this]
   simp_all
   refine (eq_inv_smul_iff₀ ?ha).mpr rfl
   have:¬ n.factorial=0 :=by exact Nat.factorial_ne_zero n
   exact Nat.cast_ne_zero.mpr this
  have:  (fun (x:ℤ_[p]) =>  Ring.multichoose (x:ℚ_[p]) n)=
     (fun (x:ℤ_[p]) => ((Nat.factorial n):ℚ)⁻¹• ( Nat.factorial n •
     Ring.multichoose (x:ℚ_[p]) n)):=by
     exact
       (Set.eqOn_univ (fun (x:ℤ_[p]) => Ring.multichoose (x:ℚ_[p]) n)
         (fun (x:ℤ_[p])=>
             (n.factorial:ℚ)⁻¹ • n.factorial • Ring.multichoose (↑x) n)).mp
         fun ⦃x⦄ _ => this x
  rw[this]
  refine (IsUnit.continuous_const_smul_iff ?hc).mpr ?_
  simp
  exact Nat.factorial_ne_zero n
  exact l2 n
lemma sj (n:ℕ ): ∀ x:ℤ_[p] ,‖Ring.multichoose (x : ℚ_[p]) n‖ ≤ 1 :=by
  intro x
  have s1:  ∀ r > 0, ∃ y:ℕ , dist x (Int.cast y) < r :=by
    intro z r
    refine DenseRange.exists_dist_lt (PadicInt.denseRange_natCast) x r
  have bib: ∀ r > 0, ∃ y:ℕ , edist x (Int.cast y) < r :=by
    intro r sr
    have: r=⊤ ∨  r<⊤ :=by exact eq_top_or_lt_top r
    rcases this with j1|j2
    use 1
    rw[j1]
    simp
    exact edist_lt_top x 1
    have: r.toReal>0 :=by
     refine ENNReal.toReal_pos_iff.mpr ?_
     constructor
     exact sr
     exact j2
    have:∃ y:ℕ , dist x (Int.cast y) < r.toReal :=by exact s1 r.toReal this
    rcases this with ⟨y,sy⟩
    use y
    have v1:dist x (Int.cast y)=(edist x (Int.cast y)).toReal :=by exact rfl
    by_contra sa
    have: edist x (Int.cast y)≥ r:=by exact le_of_not_lt sa
    have j1: (edist x (Int.cast y)).toReal≥ r.toReal :=by
     refine
      (ENNReal.toReal_le_toReal ?ha ?hb).mpr this
     exact LT.lt.ne_top j2
     exact edist_ne_top x ↑y
    rw[← v1] at j1
    have uv1: ¬ dist x ↑y < r.toReal:=by exact not_lt.mpr j1
    exact uv1 sy
  by_contra ha
  have: ‖Ring.multichoose (x : ℚ_[p]) n‖> 1 :=by exact lt_of_not_ge ha
  have u1: ‖Ring.multichoose (x : ℚ_[p]) n‖-1> 0 :=by exact sub_pos.mpr this
  have u1: (‖Ring.multichoose (x : ℚ_[p]) n‖-1).toNNReal >0:=by
   exact Real.toNNReal_pos.mpr u1
  have u1: ((‖Ring.multichoose (x : ℚ_[p]) n‖-1).toNNReal:ENNReal) >0:=by
   exact ENNReal.coe_pos.mpr u1
  have: ContinuousAt (fun (x:ℤ_[p]) =>Ring.multichoose (x:ℚ_[p]) n) x:=by
    refine Continuous.continuousAt (l3 n)
  have jp1: Filter.Tendsto (fun (x:ℤ_[p]) =>Ring.multichoose (x:ℚ_[p]) n) (nhds x)
   (nhds (Ring.multichoose (x:ℚ_[p]) n)):=by
    exact this
  rw[EMetric.tendsto_nhds_nhds] at jp1
  have dus:∃ δ > 0, ∀ ⦃x_1 : ℤ_[p]⦄, edist x_1 x < δ →
   edist (Ring.multichoose (x_1: ℚ_[p]) n) (Ring.multichoose (x: ℚ_[p]) n) <
    (‖Ring.multichoose (x : ℚ_[p]) n‖-1).toNNReal  :=by
     exact jp1 ((‖Ring.multichoose (x : ℚ_[p]) n‖-1).toNNReal:ENNReal) u1
  rcases dus with ⟨h1,h2,h3⟩
  have:∃ y:ℕ , edist x (Int.cast y) < h1:=by
    exact bib h1 h2
  rcases this with ⟨y,hy⟩
  rw[edist_comm] at hy
  have: edist (Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n) (Ring.multichoose (x: ℚ_[p]) n) <
    (‖Ring.multichoose (x : ℚ_[p]) n‖-1).toNNReal :=by
     exact h3  hy
  have sm: dist (Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n) (Ring.multichoose (x: ℚ_[p]) n) <
    (‖Ring.multichoose (x : ℚ_[p]) n‖-1) :=by
     exact edist_lt_ofReal.mp (h3 hy)
  have: dist (Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n) (Ring.multichoose (x: ℚ_[p]) n)=
   ‖(Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n)- (Ring.multichoose (x: ℚ_[p]) n)‖ :=by
   rfl
  rw[this] at sm
  have k1: ‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n - Ring.multichoose (x : ℚ_[p]) n‖ ≥ ‖Ring.multichoose (x : ℚ_[p]) n‖
   -‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n‖ :=by
     have j1:‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n - Ring.multichoose (x : ℚ_[p]) n‖ ≥ |‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n‖ -‖Ring.multichoose (x : ℚ_[p]) n‖| :=by
       rw[ge_iff_le]
       exact abs_norm_sub_norm_le (Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n) (Ring.multichoose (x: ℚ_[p]) n)
     have j2: |‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n‖ -‖Ring.multichoose (x : ℚ_[p]) n‖|≥ ‖Ring.multichoose (x : ℚ_[p]) n‖ -‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n‖:=by
       rw[abs_sub_comm]
       exact le_abs_self (‖Ring.multichoose (x : ℚ_[p]) n‖ - ‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p])  n‖)
     exact
       Preorder.le_trans (‖Ring.multichoose (x : ℚ_[p]) n‖ - ‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n‖)
         |‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n‖ - ‖Ring.multichoose (x : ℚ_[p]) n‖|
         ‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n - Ring.multichoose (x : ℚ_[p]) n‖ j2 j1
  have k2:  ‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n‖ ≤ 1 :=by
    have: Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n =Ring.multichoose y n :=by
     simp_all[Ring.multichoose, BinomialRing.multichoose]
     rw[Ring.smeval_ascPochhammer_nat_cast]
     rw[ Eq.symm (Ring.factorial_nsmul_multichoose_eq_ascPochhammer y n)]
     simp_all[Ring.multichoose, BinomialRing.multichoose]
     refine (inv_smul_eq_iff₀ (Nat.cast_ne_zero.mpr ( Nat.factorial_ne_zero n))).mpr rfl
    rw[this]
    exact IsUltrametricDist.norm_natCast_le_one ℚ_[p] (Ring.multichoose y n)
  have:‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n - Ring.multichoose (↑x) n‖≥ ‖Ring.multichoose (x : ℚ_[p]) n‖-1:=by
    exact
     Preorder.le_trans (‖Ring.multichoose (x : ℚ_[p]) n‖ - 1)
      (‖Ring.multichoose (x : ℚ_[p]) n‖ - ‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n‖)
      ‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n - Ring.multichoose (x : ℚ_[p]) n‖ (tsub_le_tsub_left k2 ‖Ring.multichoose (x : ℚ_[p]) n‖) k1
  have:¬ ‖Ring.multichoose ((y:ℤ_[p]) : ℚ_[p]) n - Ring.multichoose (↑x) n‖< ‖Ring.multichoose (x : ℚ_[p]) n‖-1:=by exact not_lt.mpr this
  exact this sm

noncomputable instance : BinomialRing ℤ_[p] where
  nsmul_right_injective := by
    intro h hn x₁ x₂ hx
    simp [hn] at hx
    exact hx
  multichoose x n := ⟨Ring.multichoose (x : ℚ_[p]) n, (by
   exact sj n x
      )⟩
  factorial_nsmul_multichoose r n := by
    ext
    change n.factorial • _ = _
    rw [Ring.factorial_nsmul_multichoose_eq_ascPochhammer]
    change (ascPochhammer ℕ n).smeval (algebraMap _ _ r) = algebraMap _ _ ((ascPochhammer ℕ n).smeval r)
    rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_algebraMap_apply]
    simp [Polynomial.aeval_eq_smeval]

noncomputable def multichoose' : ℤ_[p] → ℕ → ℤ_[p]
  | _, 0 => 1
  | x, n + 1 => BinomialRing.multichoose (x - n) (n + 1)

lemma nat_eq_choose : ∀ x n : ℕ, (multichoose' x n).val = (Nat.choose x n : ℚ_[p]) := by
  intro x n
  unfold multichoose'
  cases n with
  | zero =>
    simp
  | succ n =>
    simp
    rw [← Ring.choose_eq_nat_choose]
    unfold Ring.choose
    have : (1 : ℚ_[p]) = (1 : ℕ) := rfl
    conv =>
      enter [2, 1]
      rw [sub_add]
      rw [this]
      simp
    rfl

lemma eq_one : ∀ n : ℕ, (multichoose' (n : ℤ_[p]) n).val = 1 := by
  intro n
  rw [nat_eq_choose n n]
  simp
lemma zero: ∀ i, multichoose' (0:ℤ_[p]) (i+1)=0 :=by
  intro i
  have: (multichoose' (0:ℤ_[p]) (i+1)).val=0:=by
    have:multichoose' (0:ℤ_[p]) (i+1)=multichoose' (0:ℕ ) (i+1):=by exact rfl
    rw[this]
    rw [nat_eq_choose 0 (i+1)]
    exact rfl
  exact PadicInt.ext_iff.mpr this
lemma z1(n:ℕ ): Continuous (fun (x:ℤ_[p]) => multichoose' x n ) :=by
  unfold multichoose'
  have:n=0∨ n>0 :=by exact Nat.eq_zero_or_pos n
  rcases this with h1|h2
  rw[h1]
  dsimp
  exact continuous_const
  have:∃ j:ℕ ,n=j.succ :=by exact exists_eq_add_one.mpr h2
  rcases this with ⟨j,jh⟩
  rw[jh]
  dsimp
  have:(fun (x:ℤ_[p])  => Ring.multichoose (x - j) (j + 1))=(fun (y:ℤ_[p]) => Ring.multichoose (y) (j + 1))∘
  (fun  (x:ℤ_[p]) => x - (j:ℤ_[p])  ):=by rfl
  rw[this]
  refine Continuous.comp (continuous_induced_rng.mpr (l3 (j + 1))) (continuous_sub_right (j:ℤ_[p]))
lemma z2(n:ℕ )(a:ℚ_[p]): Continuous (fun (x:ℤ_[p]) => multichoose' x n•a ) :=by
   have:(fun (x:ℤ_[p]) => multichoose' x n•a )=(fun (y:ℤ_[p]) => y•a)∘
    (fun (x:ℤ_[p]) => multichoose' x n ) :=by rfl
   rw[this]
   refine Continuous.comp (?_) (z1 n)
   ·
     have:(fun (y:ℤ_[p]) => y•a)=(fun (y:ℤ_[p]) => y*a):=by exact rfl
     rw[this]
     have: (fun (y:ℤ_[p]) => y*a)=(fun (y:ℚ_[p]) => y*a)∘(fun (y:ℤ_[p]) => (y:ℚ_[p])):=by rfl
     rw[this]
     refine Continuous.comp (continuous_mul_right a) (continuous_iff_le_induced.mpr fun U a => a)
end multichoose'

section discrete_derivatives
variable {p : ℕ} [Fact (Nat.Prime p)]
variable{α:Type*}{β:Type*}[CommRing α][CommRing β]

def discrete_derivatives (f: α → β): ℕ → α → β
  | 0 , a => f a

  | n+1, a  => discrete_derivatives f n (a+1)- discrete_derivatives f n a

def coff_in_poly (f: α → β)(n:ℕ ) := discrete_derivatives f n (0:α)

lemma  disrv (f: α → β)(m:ℕ )(n:ℕ ) :∀ a:α ,discrete_derivatives (discrete_derivatives f  m ) n a=discrete_derivatives f (m+n) a:=by
  induction' n with n ih
  · intro a
    rfl
  · intro a
    have ud1: discrete_derivatives (discrete_derivatives f m) (n + 1) a =  discrete_derivatives (discrete_derivatives f m) n (a+1) -  discrete_derivatives (discrete_derivatives f m) n a :=by
     exact rfl
    rw[ud1]
    rw[ih  (a+1)]
    rw[ih a]
    rfl



def ds (f: α → β)(s:α): ℕ → ℕ → β :=
  fun x y => (-1) ^ x• f (s+y•(1:α ))
lemma pro1 (f: α → β)(n:ℕ):∀ s:α , discrete_derivatives f n s= ∑ i ∈ Finset.range (n + 1), (n.choose i) • ((-1) ^ (i ) • f (s + (n - i)•(1:α))) :=by
 induction' n with n ih
 · intro  s
   simp
   rfl
 · intro s
   have sh1: discrete_derivatives f (n+1) s =discrete_derivatives f n (s+1)-discrete_derivatives f n s := rfl
   rw[sh1]
   rw[ih]
   rw[ih]
   have  uug:  ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i) • ds f s i (n + 1 - i) = ∑ i ∈Finset.range (n + 1), (n.choose i) • ds f s i (n + 1 - i) + ∑ i ∈ Finset.range (n + 1), (n.choose i) • ds f s (i + 1) (n - i):=by exact Finset.sum_choose_succ_nsmul (ds f s) n
   unfold ds at uug
   have ds2 :  ∑ i ∈ Finset.range (n + 1 + 1), ((n + 1).choose i) • (-1) ^ i  • f (s + (n + 1 - i)•1)=∑ x ∈ Finset.range (n + 2), ((n + 1).choose x) •(-1) ^ x •f (s + (n + 1 - x)•1):=rfl
   rw [ds2]
   rw[uug]
   rw[sub_eq_add_neg,← Finset.sum_neg_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.sum_congr _]
   intro i hi
   have: s + 1 + (n - i) • 1=s + (1+ n - i) • 1 :=by
      refine  Mathlib.Tactic.Ring.add_pf_add_lt s ?_
      have: 1=1•(1:α) :=by exact Eq.symm (one_nsmul 1)
      nth_rw 1 [this]
      have gg: (n - i)≤ (1+ n - i)  :=by
       refine Nat.sub_le_sub_right (Nat.le_add_left n 1) i
      have : 1=1+ n - i -(n - i) :=by
        refine Eq.symm (Nat.sub_eq_of_eq_add' ?h)
        ring_nf
        refine Nat.add_sub_assoc (Finset.mem_range_succ_iff.mp hi) 1
      nth_rw 1 [this]
      exact sub_nsmul_nsmul_add 1 gg
   have uu1:1+ n - i=n+1-i :=by abel_nf
   rw[uu1] at this
   rw[this]
   congr
   refine neg_eq_of_add_eq_zero_right ?succ.e_a.a
   simp
   ring_nf
   simp


lemma pro2 (f: α → β): coff_in_poly f n = ∑ i ∈ Finset.range (n + 1), (n.choose i) • ((-1) ^ (i ) • f ( (n - i)• 1)) :=by
  unfold  coff_in_poly
  rw[pro1 f  n  0]
  simp

lemma pro4_1 (f: α → β)(ss :n≥ 1):∀ s:α , discrete_derivatives f n s= f (s+n•1) + ∑ i ∈ Finset.range (n -1), (n.choose (i+1)) •
 ((-1) ^ (i+1 ) • f (s+ (n - (i+1))• 1)) + (-1)^n• f s:=by
   intro s
   rw[pro1]
   have ds1 : ∑ i ∈ Finset.range (n + 1), (n.choose i) • ((-1) ^ (i ) • f ( s+(n - i)• 1))=∑ i ∈ Finset.range (n ), (n.choose i) • ((-1) ^ (i ) • f (s+ (n - i)• 1))+ (-1)^n• f s :=by
    nth_rw 1 [Finset.sum_range_succ]
    simp
   rw[ds1]
   have ds2 : ∑ i ∈ Finset.range (n ), (n.choose i) • ((-1) ^ (i ) • f ( s+(n - i)• 1))=f (s+n•1)+
  ∑ i ∈ Finset.range (n-1), (n.choose (i+1)) • ((-1) ^ (i+1 ) • f (s+ (n - (i+1))• 1)):=by
    have: n=(n-1)+1:=by exact (Nat.sub_eq_iff_eq_add ss).mp rfl
    nth_rw 1 [this]
    nth_rw 1 [Finset.sum_range_succ']
    simp
    ring
   rw[ds2]



lemma pro4 (f: α → β)(ss :n≥ 1):  coff_in_poly f n = f (n•1) + ∑ i ∈ Finset.range (n -1), (n.choose (i+1)) •
 ((-1) ^ (i+1 ) • f ( (n - (i+1))• 1)) + (-1)^n• f 0 :=by
  rw[pro2]
  have ds1 : ∑ i ∈ Finset.range (n + 1), (n.choose i) • ((-1) ^ (i ) • f ( (n - i)• 1))=∑ i ∈ Finset.range (n ), (n.choose i) • ((-1) ^ (i ) • f ( (n - i)• 1))+ (-1)^n• f 0 :=by
   nth_rw 1 [Finset.sum_range_succ]
   simp
  rw[ds1]
  have ds2 : ∑ i ∈ Finset.range (n ), (n.choose i) • ((-1) ^ (i ) • f ( (n - i)• 1))=f (n•1)+
  ∑ i ∈ Finset.range (n-1), (n.choose (i+1)) • ((-1) ^ (i+1 ) • f ( (n - (i+1))• 1)):=by
    have: n=(n-1)+1:=by exact (Nat.sub_eq_iff_eq_add ss).mp rfl
    nth_rw 1 [this]
    nth_rw 1 [Finset.sum_range_succ']
    simp
    ring
  rw[ds2]


lemma summable_th1_1 (a:ℕ → ℚ_[p])(hs : Summable a)(n:ℕ ) :  Summable (fun x => a (n+x)):=by
  have: (fun x => a (x+n))=(fun x => a (n+x)) :=by
    have:∀ b:ℕ , (fun x => a (x+n)) b=(fun x => a (n+x)) b :=by
     intro b
     simp
     ring_nf
    exact (Set.eqOn_univ (fun x => a (x + n)) fun x => a (n + x)).mp fun ⦃x⦄ _ => this x
  rw[← this]
  exact (summable_nat_add_iff n).mpr hs

lemma summable_th2 (a:ℕ → ℚ_[p])(b:ℕ → ℤ_[p])(hs : Summable a) :  Summable (fun x => b x• a x ):=by
   rw[summable_in_p_adic_field] at hs
   rw[summable_in_p_adic_field]
   have jp1: ∀ i, ‖ (b i • a i )‖ ≤ ‖a i‖  :=by
      intro i
      have: b i• a i=b i * a i :=by
        exact rfl
      rw[this]
      have:‖ b i * a i‖ = ‖(b i: ℚ_[p])‖*‖ a i‖:=by exact padicNormE.mul (↑(b i)) (a i)
      rw[this]
      have :‖(b i: ℚ_[p])‖≤ 1 :=by
        simp
        exact PadicInt.norm_le_one (b i)
      have:‖(b i: ℚ_[p])‖* ‖a i‖≤ 1* ‖a i‖ :=by
       refine mul_le_mul_of_nonneg this (Preorder.le_refl ‖a i‖) ( norm_nonneg ↑(b i))
         (norm_nonneg (a i))
      have one:1* ‖a i‖=‖a i‖ :=by exact one_mul ‖a i‖
      rw[one] at this
      exact this
   rw[EMetric.tendsto_atTop]
   rw[EMetric.tendsto_atTop] at hs
   intro w sw
   have jp2: ∃ N, ∀ n ≥ N, edist ‖ a n‖ 0 < w :=by  exact hs w sw
   rcases jp2 with ⟨N,iN⟩
   use N
   intro n hn
   have jp3 : edist ‖ a n‖ 0 < w :=by exact iN n hn
   rw[edist_eq_coe_nnnorm_sub] at jp3
   simp at jp3
   rw[edist_eq_coe_nnnorm_sub]
   simp
   have :‖a n‖₊=‖a n‖.toNNReal :=by exact Eq.symm norm_toNNReal
   rw[this] at jp3
   have :‖b n• a n‖₊=‖b n• a n‖.toNNReal :=by exact Eq.symm norm_toNNReal
   rw[this]
   have : ‖b n • a n‖.toNNReal≤ ‖a n‖.toNNReal :=by
     exact Real.toNNReal_le_toNNReal (jp1 n)
   have : ENNReal.ofNNReal ‖b n•a n‖.toNNReal≤ ENNReal.ofNNReal ‖a n‖.toNNReal :=by
     exact ENNReal.coe_le_coe.mpr this
   exact lt_of_le_of_lt this jp3
lemma summable_th3 (a:ℕ → ℚ_[p])(b:ℕ → ℤ_[p])(hs : Summable a)(n:ℕ ) :
Summable (fun x => b x• a (n+x) ):=by
 have jp0:Summable (fun x => a (n+x)) :=by exact summable_th1_1 a hs n
 rw[summable_in_p_adic_field] at jp0
 rw[summable_in_p_adic_field]
 have jp1: ∀ i, ‖ (b i • a (n+i) )‖ ≤ ‖a (n+i)‖  :=by
      intro i
      have: b i• a (n+i)=b i * a (n+i) :=by
        exact rfl
      rw[this]
      have:‖ b i * a (n+i)‖ = ‖(b i: ℚ_[p])‖*‖ a (n+i)‖:=by exact padicNormE.mul (↑(b i)) (a (n+i))
      rw[this]
      have :‖(b i: ℚ_[p])‖≤ 1 :=by
        simp
        exact PadicInt.norm_le_one (b i)
      have:‖(b i: ℚ_[p])‖* ‖a (n+i)‖≤ 1* ‖a (n+i)‖ :=by
       refine mul_le_mul_of_nonneg this (Preorder.le_refl ‖a (n+i)‖) ( norm_nonneg ↑(b i))
         (norm_nonneg (a (n+i)))
      have one:1* ‖a (n+i)‖=‖a (n+i)‖ :=by exact one_mul ‖a (n+i)‖
      rw[one] at this
      exact this
 rw[EMetric.tendsto_atTop]
 rw[EMetric.tendsto_atTop] at jp0
 intro w sw
 have jp2: ∃ N, ∀ i ≥ N, edist ‖ a (n+i)‖ 0 < w :=by  exact jp0 w sw
 rcases jp2 with ⟨N,iN⟩
 use N
 intro i hi
 have jp3 : edist ‖ a (n+i)‖ 0 < w :=by exact iN i hi
 rw[edist_eq_coe_nnnorm_sub] at jp3
 simp at jp3
 rw[edist_eq_coe_nnnorm_sub]
 simp
 have :‖a (n+i)‖₊=‖a (n+i)‖.toNNReal :=by exact Eq.symm norm_toNNReal
 rw[this] at jp3
 have :‖b i• a (n+i)‖₊=‖b i• a (n+i)‖.toNNReal :=by exact Eq.symm norm_toNNReal
 rw[this]
 have : ‖b i• a (n+i)‖.toNNReal≤ ‖a (n+i)‖.toNNReal :=by
   exact
    Real.toNNReal_le_toNNReal (jp1 i)
 have : ENNReal.ofNNReal ‖b i• a (n+i)‖.toNNReal≤  ENNReal.ofNNReal ‖a (n+i)‖.toNNReal
   :=by
     exact ENNReal.coe_le_coe.mpr this
 exact lt_of_le_of_lt this jp3
lemma d_d_mulchs (a:ℕ → ℚ_[p])(hs : Summable a)(n:ℕ ):∀ x:ℤ_[p] ,
discrete_derivatives (fun (x:ℤ_[p]) => ∑' i : ℕ, (multichoose'  x  i  )•a i ) n x =
∑' i : ℕ, (multichoose'  x  i )•a (n+i)  :=by
  induction' n with n ih
  · unfold discrete_derivatives
    simp
  · intro x
    have : discrete_derivatives (fun (x:ℤ_[p]) => ∑' i : ℕ, (multichoose'  x  i  )•a i ) (n + 1) x=
    discrete_derivatives (fun (x:ℤ_[p]) => ∑' i : ℕ, (multichoose'  x  i  )•a i ) n (x+1)-discrete_derivatives (fun (x:ℤ_[p]) => ∑' i : ℕ, (multichoose'  x  i  )•a i ) n x :=by exact rfl
    rw[this]
    rw[ih (x+1)]
    rw[ih x]
    have: ∑' (i : ℕ), multichoose' (x + 1) i • a (n+i) - ∑' (i : ℕ), multichoose' x i •
    a ( n+i ) = ∑' (i : ℕ),( multichoose' (x + 1) i • a (n+i)-multichoose' x i • a (n+i)) :=by
      rw[sub_eq_add_neg]
      rw[← tsum_neg]
      rw[← tsum_add]
      rw[tsum_congr]
      intro b
      ring
      exact summable_th3 a (fun i=>  multichoose' (x + 1) i ) hs n
      have : (fun (b:ℕ) => -(multichoose' x b • a (n + b)) )= (fun (b:ℕ) =>
       -(multichoose' x b) • a (n + b)):=by
         have ra:∀ b:ℕ , (fun (b:ℕ) => -(multichoose' x b • a (n + b)) ) b=
         (fun (b:ℕ) => -(multichoose' x b) • a (n + b)) b :=by
          intro b
          simp
         exact
           (Set.eqOn_univ (fun b => -(multichoose' x b • a (n + b))) fun b =>
                 -multichoose' x b • a (n + b)).mp
             fun ⦃x⦄ _ => ra x
      rw[this]
      exact summable_th3 a (fun (b:ℕ)=>  -(multichoose' x b) ) hs n
    rw[this]
    have: ∑' (i : ℕ),( multichoose' (x + 1) i • a (n+i)-multichoose' x i • a (n+i))=∑' (i : ℕ),
    ( (multichoose' (x + 1) i  -multichoose' x i )• a (n+i)) :=by
       rw[tsum_congr]
       intro b
       exact Eq.symm (sub_smul (multichoose' (x + 1) b) (multichoose' x b) (a (n + b)))
    rw[this]
    have: ∑' (i : ℕ),( (multichoose' (x + 1) i  -multichoose' x i )• a (n+i)) =
     ( (multichoose' (x + 1) 0  -multichoose' x 0 )• a (n+0)) +∑' (i : ℕ),
     ( (multichoose' (x + 1) (i+1)  -multichoose' x (i+1) )  )• a (n+i+1) :=by
       have ds:Summable (fun (i:ℕ ) =>( (multichoose' (x + 1) i  -multichoose' x i )• a (n+i))):=by
         exact summable_th3 a (fun x_1 => multichoose' (x + 1) x_1 - multichoose' x x_1) hs n
       exact tsum_eq_zero_add ds
    rw[this]
    have: multichoose' x 0 =1 :=rfl
    rw[this]
    have: multichoose' (x+1) 0 =1 :=rfl
    rw[this]
    have: ∀ i:ℕ ,multichoose' (x + 1) (i+1)  -multichoose' x (i+1) =multichoose' x i :=by
      intro i
      by_cases h : i = 0
      rw[h]
      unfold  multichoose'
      simp
      have:∃ a:ℕ , i=a+1 :=by exact exists_eq_succ_of_ne_zero h
      rcases this with ⟨a,ss⟩
      rw[ss]
      unfold  multichoose'
      simp
      have : x-a=x-(a+1)+1 :=by
        ring
      nth_rw 1 [this]
      rw[Ring.multichoose_succ_succ]
      simp
      rw[← this]

    have: ∑' (i : ℕ),( (multichoose' (x + 1) (i+1)  -multichoose' x (i+1) )  )• a (n+i+1)=
    ∑' (i : ℕ),( multichoose' x i )• a (n+i+1) :=by
       rw[tsum_congr]
       intro b
       rw[this]
    rw[this]
    simp
    ring_nf

end discrete_derivatives

section p_adic_summable
variable (p:ℕ )[Fact (Nat.Prime p)]
--lim i → +OO     ||a i||=0
variable {a : ℕ → ℚ_[p]}
lemma summable_f (a:ℕ →ℚ_[p]): Summable a ↔ Filter.Tendsto (fun (x :ℕ ) => ‖a x‖) Filter.atTop
(nhds 0)  :=by
   constructor
   · intro ha
     rw[summable_iff_vanishing_norm]at ha
     rw[EMetric.tendsto_atTop]
     intro w sw
     have :w=⊤ ∨ ¬ w=⊤ :=by exact eq_or_ne w ⊤
     rcases this with g1|g2
     · use 0
       intro j
       rw[edist_eq_coe_nnnorm_sub]
       simp
       rw[g1]
       exact ENNReal.coe_lt_top
     · have jp0: w.toReal >0 :=by
        refine ENNReal.toReal_pos (Ne.symm (ne_of_lt sw)) g2
       have jp1: ∃ s, ∀ (t : Finset ℕ), Disjoint t s → ‖∑ i ∈ t, a i‖ < w.toReal :=by
        exact ha  w.toReal jp0
       rcases jp1 with ⟨s,ds⟩
       have jp2 :∃ N:ℕ ,∀ n>N , Disjoint {n} s :=by
        have jp01: ∃ n, s ⊆ Finset.range n :=by
          exact Finset.exists_nat_subset_range s
        rcases jp01 with ⟨n,hn⟩
        use n
        intro m hm
        have : Disjoint {m} (Finset.range n ) :=by
         refine Finset.disjoint_singleton_left.mpr ?_
         by_contra ds
         have j1: m<n :=by exact List.mem_range.mp ds
         have j2:¬ m<n :=by exact Nat.not_lt_of_gt hm
         exact j2 j1
        have: Disjoint {m} s :=by
         exact
          Disjoint.symm
          (Finset.disjoint_of_subset_left hn (id (Disjoint.symm this)))
        exact this
       rcases jp2 with ⟨N,dN⟩
       have jp21:∀ n ≥ (N+1),Disjoint {n} s :=by
        intro n dn
        have:n>N :=by exact dn
        exact dN n this
       use (N+1)
       intro n dn
       have jp3 : ‖∑ i ∈ {n}, a i‖ < w.toReal :=by
         have :Disjoint {n} s :=by exact jp21  n dn
         exact ds {n} this
       simp at jp3
       rw[edist_eq_coe_nnnorm_sub]
       simp
       have jp31:(‖a n‖.toNNReal:ENNReal) <ENNReal.ofReal (w.toReal):=by
        refine ENNReal.coe_lt_coe_of_lt ?_
        exact (Real.toNNReal_lt_toNNReal_iff jp0).mpr jp3
       have : ‖a n‖.toNNReal=‖a n‖₊ :=by exact norm_toNNReal
       rw[this] at jp31
       have: ENNReal.ofReal (w.toReal)=w :=by
         exact ENNReal.ofReal_toReal_eq_iff.mpr g2
       rw[this] at jp31
       exact jp31
   · intro ha
     rw[summable_iff_vanishing_norm]
     intro w hw
     have jp1:∃ n:ℕ ,∀ i>n ,‖a i‖ ≤  w /2:=by
       have: ∀ ε > 0, ∃ N, ∀ n ≥ N, edist ‖a n‖ 0 < ε:=by
         exact EMetric.tendsto_atTop.mp ha
       have :∃ N, ∀ n ≥ N, edist ‖a n‖ 0 <(w/2).toNNReal:=by
         have s1: (w/2).toNNReal>0 :=by
           refine Real.toNNReal_pos.mpr ?_
           exact half_pos hw
         have s2 :((w / 2).toNNReal:ENNReal) > 0:=by
           exact ENNReal.coe_pos.mpr s1
         exact this (w/2).toNNReal s2
       rcases this with ⟨n,hn⟩
       use n-1
       intro i si
       have ds1:i≥ n :=by exact Nat.le_of_pred_lt si
       have u1: edist ‖a i‖ 0 <(w/2).toNNReal :=by exact hn i ds1
       rw[edist_eq_coe_nnnorm_sub] at u1
       simp at u1
       have u2: ‖a i‖ <w / 2 :=by
         refine (Real.toNNReal_lt_toNNReal_iff_of_nonneg ?hr).mp ?_
         · exact norm_nonneg (a i)
         · have: ‖a i‖₊=‖a i‖.toNNReal :=by exact Eq.symm norm_toNNReal
           rw[←this]
           exact u1
       exact le_of_lt u2

     rcases jp1 with ⟨n1,hn1⟩
     use Finset.range (n1+1)
     intro t hst
     have jp2:∀ h ∈  t , h>n1 :=by
       intro h hs
       by_contra u1
       have : h≤ n1 :=by exact Nat.le_of_not_lt u1
       have : h <n1+1 :=by exact Order.lt_add_one_iff.mpr this
       have :  h∈ Finset.range (n1+1) :=by
         refine Finset.mem_range.mpr this
       have : ¬  Disjoint t (Finset.range (n1 + 1)) :=by
         refine Finset.not_disjoint_iff.mpr ?_
         use h
       exact this hst
     have jp3 :∀ h∈  t , ‖a h‖ ≤  w/2 :=by
       intro h hs
       exact hn1 h (jp2 h hs)
     rcases Finset.eq_empty_or_nonempty t with g1|g2
     · rw[g1]
       simp
       exact hw
     ·  have jp5: ‖∑ i ∈ t, a i‖ ≤  w/2 :=by refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty g2  jp3
        have jp6: w/2< w :=by exact div_two_lt_of_pos hw
        exact lt_of_le_of_lt jp5 jp6
end  p_adic_summable
section is_continue_for_summable_multchoose
variable (p:ℕ )[ds:Fact (Nat.Prime p)]
variable {a : ℕ → ℚ_[p]}
lemma Padic_int_tsum (ha:Summable a)(z:ℝ)(sa:z>0):(∀ i:ℕ ,‖a i‖ < z)→ ‖∑' i : ℕ , (a i)‖≤ z :=by
 intro u
 have q1:∀ n:ℕ , ‖∑ i  ∈ Finset.range n, a i‖ <z :=by
    intro n
    rcases (Nat.eq_zero_or_pos n) with j1|j2
    rw[j1]
    simp
    exact sa
    have df1:∀  i ∈ Finset.range n ,‖a i‖  <z :=by
     intro i
     exact fun a => u i
    have n1: (Finset.range n).Nonempty:=by
      refine Finset.Aesop.range_nonempty (not_eq_zero_of_lt j2)
    have: ‖∑ i ∈ Finset.range n, a i‖< z :=by
       sorry
    exact this
 by_contra hg
 have q2:  ‖∑' (i : ℕ), a i‖ > z :=by exact lt_of_not_ge hg
 have q3: HasSum a (∑' (i : ℕ), a i) :=by exact Summable.hasSum ha
 have: Filter.Tendsto (fun n => ∑ i  ∈ Finset.range n, a i)  Filter.atTop  (nhds (∑' (i : ℕ), a i)) :=by
   exact HasSum.Multipliable.tendsto_sum_tsum_nat ha
 rw[EMetric.tendsto_atTop] at this
 have: ∃ N, ∀ n ≥ N, edist (∑ i ∈ Finset.range n, a i) (∑' (i : ℕ), a i) < (‖∑' (i : ℕ), a i‖ - z).toNNReal :=by
   sorry
 rcases this with ⟨N,hn⟩
 have jk:  edist (∑ i ∈ Finset.range N, a i) (∑' (i : ℕ), a i) <(‖∑' (i : ℕ), a i‖ - z).toNNReal:=by sorry
 have jk:  dist (∑ i ∈ Finset.range N, a i) (∑' (i : ℕ), a i) <(‖∑' (i : ℕ), a i‖ - z):=by sorry
 have: dist (∑ i ∈ Finset.range N, a i) (∑' (i : ℕ), a i)=‖(∑ i ∈ Finset.range N, a i)-(∑' (i : ℕ), a i)‖ :=by exact
   rfl
 rw[this] at jk
 have: ‖∑ i ∈ Finset.range N, a i - ∑' (i : ℕ), a i‖ >‖∑ i ∈ Finset.range N, a i‖-‖∑' (i : ℕ), a i‖ :=by sorry
 sorry



lemma is_continue_for_summable_multchoose(ha:Summable a): Continuous
  (fun (x:ℤ_[p]) => (∑' i : ℕ ,(multichoose'  x  i  )• a i )  ) :=by
    rw[continuous_iff_continuousAt]
    intro x
    have: Filter.Tendsto (fun (x:ℤ_[p]) => (∑' i : ℕ ,(multichoose'  x  i  )• a i )  ) (nhds x) ( nhds (∑' i : ℕ ,(multichoose'  x  i  )• a i ) ):=by
       rw[NormedAddCommGroup.tendsto_nhds_nhds]
       intro z sz1
       have sz :(z/2)>0 :=by exact half_pos sz1
       have: Filter.Tendsto (fun (x :ℕ ) => ‖a x‖) Filter.atTop (nhds 0) :=by
           exact (summable_f p a).mp ha
       rw[EMetric.tendsto_atTop] at this
       have: ∀ ε > 0, ∃ N,N>0∧∀ n ≥ N,  ‖a n‖  < ε :=by
         intro z sz
         have: ∃ N, ∀ n ≥ N,  edist ‖a n‖ 0  < z.toNNReal :=by
           exact this (z.toNNReal:ENNReal) (ENNReal.coe_pos.mpr (Real.toNNReal_pos.mpr sz))
         rcases this with ⟨N,hN⟩
         use N+1
         constructor
         · simp
         · intro n sn
           have: n≥ N:=by exact le_of_succ_le sn
           have:dist ‖a n‖ 0 <z :=by exact edist_lt_ofReal.mp (hN n (le_of_succ_le sn))
           simp at this
           exact this
       have: ∃ N, N>0∧∀ n ≥ N,  ‖a n‖  < z/2 :=by exact this (z/2) sz
       rcases this with ⟨N1,⟨hN1,hN2⟩⟩
       have h : ∀ n:ℕ ,∃ δ > 0, ∀ (x' : ℤ_[p]), ‖x' - x‖ < δ → ‖multichoose' x' n • a n -  multichoose' x n • a n‖ < z/2 :=by
         intro n
         have: Continuous (fun (x:ℤ_[p]) => multichoose' x n • a n) :=by
          exact z2 n (a n)
         rw[continuous_iff_continuousAt] at this
         have: Filter.Tendsto (fun x => multichoose' x n • a n) (nhds x)
          (nhds ( multichoose' x n • a n)) :=by
            exact this x
         rw[NormedAddCommGroup.tendsto_nhds_nhds] at this
         exact this (z/2) sz
       let hs (n : ℕ) := (h n).choose
       have hp (n : ℕ) : hs n > 0 ∧ ∀ (x' : ℤ_[p]), ‖x' - x‖ < (hs n) →
         ‖multichoose' x' n • a n -  multichoose' x n • a n‖ < z/2:= (h n).choose_spec

       have: ∃ δ > 0,  ∀ n: Fin N1 ,∀ (x' : ℤ_[p]), ‖x' - x‖ < δ →
        ‖multichoose' x' n • a n -  multichoose' x n • a n‖ < z/2:=by
           have: ∃ x₀:Fin N1, ∀ (x : Fin N1), hs x₀ ≤ hs x :=by
             have:Nonempty (Fin N1) :=by
               exact Fin.pos_iff_nonempty.mp hN1
             exact Finite.exists_min fun (x : Fin N1) => hs (x : Fin N1)
           rcases this with ⟨c,hj⟩
           use (hs c)
           constructor
           · exact (hp c).1
           · intro n
             have: hs c ≤ hs n :=by exact hj n
             intro r ser
             have: ‖r-x‖ < hs n :=by exact gt_of_ge_of_gt (hj n) ser
             exact (hp n).2 r this
       rcases this with ⟨d2,⟨sd1,sd2⟩⟩
       use d2
       constructor
       · exact sd1
       · intro u su
         have: ∑' (i : ℕ), multichoose' u i • a i - ∑' (i : ℕ), multichoose' x i • a i=
         ∑' (i : ℕ),(multichoose' u i • a i - multichoose' x i • a i):=by
          refine Eq.symm (tsum_sub (summable_th2 a (multichoose' u) ha)
           (summable_th2 a (multichoose' x) ha))
         rw[this]
         have f1: ∀ i:ℕ ,‖multichoose' u i • a i - multichoose' x i • a i‖ < z/2:=by
           intro i
           have: i≥ N1 ∨ i < N1 :=by exact le_or_lt N1 i
           rcases this with j1|j2
           · have: multichoose' u i • a i - multichoose' x i • a i=(multichoose' u i  - multichoose' x i) • a i
             :=by exact Eq.symm (sub_smul (multichoose' u i) (multichoose' x i) (a i))
             rw[this]
             have: ‖(multichoose' u i - multichoose' x i) • a i‖ =‖(multichoose' u i - multichoose' x i)‖*‖ a i‖
              :=by sorry
             rw[this]
             have:  ‖multichoose' u i - multichoose' x i‖≤ 1 :=by exact PadicInt.norm_le_one (multichoose' u i - multichoose' x i)
             have dj1: ‖multichoose' u i - multichoose' x i‖ * ‖a i‖≤ 1*‖a i‖ :=by sorry
             simp at dj1
             have j2: ‖a i‖ < z/2 :=by exact hN2 i j1
             exact LE.le.trans_lt dj1 j2
           · have: ∃ j:Fin N1 , i=j:=by
              refine Fin.exists_iff.mpr ?_
              use i
              exact exists_apply_eq_apply (fun a => i) j2
             rcases this with ⟨j,hj⟩
             rw[hj]
             exact sd2 j u su
         have: Summable (fun i => (multichoose' u i • a i - multichoose' x i • a i)):=by sorry
         have t1:‖∑' (i : ℕ), (multichoose' u i • a i - multichoose' x i • a i)‖ ≤ z / 2:=Padic_int_tsum p this (z/2) sz f1
         have t2: z/2 <z :=by exact div_two_lt_of_pos sz1
         exact lt_of_le_of_lt t1 t2

    exact this







end is_continue_for_summable_multchoose
section bijective
variable {p : ℕ} [Fact (Nat.Prime p)]


def bound_a :Set (ℕ → ℚ_[p]):={a | Summable a}

def fun_c_f_to_bound_a : C(ℤ_[p], ℚ_[p]) →  bound_a (p := p) := by
   intro ⟨f,fa⟩
   have : Continuous f :=by exact fa
   use (fun (n:ℕ ) => coff_in_poly f n)
   have: Filter.Tendsto (fun (n : ℕ) => ‖(coff_in_poly f n)‖) Filter.atTop (nhds 0) :=by sorry
   have: Summable (fun (n:ℕ ) => coff_in_poly f n) :=by
     exact (summable_f p fun n => coff_in_poly f n).mpr this
   exact this
lemma bij : (fun_c_f_to_bound_a (p := p)).Bijective  :=by
  rw[Function.bijective_iff_existsUnique]
  intro ⟨a,ha⟩
  refine ExistsUnique.intro ⟨(fun (x:ℤ_[p]) => ∑' i : ℕ ,(multichoose'  x  i  )• a i),
       (is_continue_for_summable_multchoose p ha)⟩ ?h₁ ?h₂
  unfold fun_c_f_to_bound_a
  dsimp
  have:∀ n:ℕ ,  coff_in_poly (fun (x:ℤ_[p]) => ∑' (i : ℕ), multichoose' x i • a i) n = a n :=by
    intro n
    sorry
  have: (fun n => coff_in_poly (fun (x:ℤ_[p]) => ∑' (i : ℕ), multichoose' x i • a i) n)=a :=by
    exact
      (Set.eqOn_univ (fun n => coff_in_poly (fun (x:ℤ_[p]) => ∑' (i : ℕ), multichoose' x i • a i) n) a).mp
        fun ⦃x⦄ a => this x
  exact SetCoe.ext this
  intro ⟨y1,y2⟩ sy
  unfold  fun_c_f_to_bound_a at sy
  simp at sy
  have gmui(s:ℤ_[p] → ℚ_[p])( rg:Continuous s): (fun n => coff_in_poly s n)=0 ↔ s=0 :=by
     constructor
     · intro rx
       have d1:coff_in_poly s 0=0 :=by
        exact
         (AddSemiconjBy.eq_zero_iff (coff_in_poly s 0)
               (congrFun (congrArg HAdd.hAdd (congrFun rx 0)) (coff_in_poly s 0))).mpr
           rfl
       unfold coff_in_poly at (d1)
       unfold discrete_derivatives at d1
       have d2:∀ n:ℕ ,coff_in_poly s n=0 :=by exact fun n => congrFun rx n
       have mmu:∀ x:ℕ , s x =0 :=by
         intro n
         induction' n using Nat.case_strong_induction_on with n ih
         have: s (0:ℕ )=s 0 :=by exact rfl
         rw[this]
         exact d1
         have: n+1≥ 1 :=by simp
         have d1m: coff_in_poly s (n+1) =
          s ((n+1) • 1) + ∑ i ∈ Finset.range ((n+1) - 1),
          n.choose (i + 1) • (-1) ^ (i + 1) • s (((n+1) - (i + 1)) • 1) + (-1) ^ (n+1) • s 0:=by sorry
         have: ∑ i ∈ Finset.range ((n+1) - 1), n.choose (i + 1) • (-1) ^ (i + 1) • s (((n+1) - (i + 1)) • 1)
           =0 :=by
            refine Finset.sum_eq_zero ?h
            intro j dj
            have: s ((n + 1 - (j + 1)) • 1)=0  :=by sorry
            rw[this]
            simp
         rw[this] at d1m
         have: s (0:ℕ )=s 0 :=by exact rfl
         rw[d1] at d1m
         rw[d2 (n+1)] at d1m
         simp at d1m
         simp
         exact id (Eq.symm d1m)
       have:∀ x:ℤ_[p], s x =0 :=by
         intro x
         by_contra sa
         have:‖s x‖ >0 := by exact norm_pos_iff.mpr sa
         have:‖s x‖.toNNReal  >0:=by exact Real.toNNReal_pos.mpr this
         have: (‖s x‖.toNNReal :ENNReal) >0:=by exact ENNReal.coe_pos.mpr this
         have s1:  ∀ r > 0, ∃ y:ℕ , dist x y < r :=by
              intro z r
              refine DenseRange.exists_dist_lt (PadicInt.denseRange_natCast) x r
         have bib: ∀ r > 0, ∃ y:ℕ , edist x y < r :=by
              intro r sr
              have: r=⊤ ∨  r<⊤ :=by exact eq_top_or_lt_top r
              rcases this with j1|j2
              use 1
              rw[j1]
              simp
              exact edist_lt_top x 1
              have: r.toReal>0 :=by
               refine ENNReal.toReal_pos_iff.mpr ?_
               constructor
               exact sr
               exact j2
              have:∃ y:ℕ , dist x (Int.cast y) < r.toReal :=by exact s1 r.toReal this
              rcases this with ⟨y,sy⟩
              use y
              have v1:dist x (Int.cast y)=(edist x (Int.cast y)).toReal :=by exact rfl
              by_contra sa
              have: edist x (Int.cast y)≥ r:=by exact le_of_not_lt sa
              have j1: (edist x (Int.cast y)).toReal≥ r.toReal :=by
                refine
                 (ENNReal.toReal_le_toReal ?ha ?hb).mpr this
                exact LT.lt.ne_top j2
                exact edist_ne_top x ↑y
              rw[← v1] at j1
              have uv1: ¬ dist x ↑y < r.toReal:=by exact not_lt.mpr j1
              exact uv1 sy
         have jp1: Filter.Tendsto (fun (x:ℤ_[p]) => s x) (nhds x)
              (nhds (s x)):=by exact Continuous.tendsto' rg x (s x) rfl
         rw[EMetric.tendsto_nhds_nhds] at jp1
         rcases (jp1 ‖s x‖.toNNReal this) with ⟨h1,h2,h3⟩
         rcases (bib h1 h2) with ⟨t,nt⟩
         rw[edist_comm] at nt
         have:¬ edist (s t) (s x) < ‖s x‖.toNNReal :=by
           by_contra sa

           have: edist (s t) (s x)=‖s x‖.toNNReal :=by
             rw[mmu t]
             rw[edist_comm]
             rw[edist_eq_coe_nnnorm]
             rw[← norm_toNNReal]
           rw[this] at sa
           have:  (‖s x‖.toNNReal:ENNReal)  =‖s x‖.toNNReal :=by exact rfl
           have:¬ (‖s x‖.toNNReal:ENNReal)<‖s x‖.toNNReal :=by exact not_lt_of_gt sa
           exact this sa
         exact this (h3 nt)
       exact (Set.eqOn_univ s 0).mp fun ⦃x⦄ a => this x
     · intro x
       unfold coff_in_poly
       sorry
  have: y1 =(fun x => ∑' (i : ℕ), multichoose' x i • a i):=by
    have th1: (fun n => coff_in_poly (y1-(fun x => ∑' (i : ℕ), multichoose' x i • a i)) n)
      =(fun n => coff_in_poly (y1) n)-
        (fun n => coff_in_poly (fun (x:ℤ_[p]) => ∑' (i : ℕ), multichoose' x i • a i) n):=by
        have:∀ n,coff_in_poly (y1-(fun x => ∑' (i : ℕ), multichoose' x i • a i)) n=
           coff_in_poly (y1) n-coff_in_poly (fun (x:ℤ_[p]) => ∑' (i : ℕ), multichoose' x i • a i) n
            :=by sorry
        exact
          (Set.eqOn_univ
                (fun n => coff_in_poly (y1 - fun x => ∑' (i : ℕ), multichoose' x i • a i) n)
                ((fun n => coff_in_poly y1 n) - fun n =>
                  coff_in_poly (fun x => ∑' (i : ℕ), multichoose' x i • a i) n)).mp
            fun ⦃x⦄ a => this x
    have th2: (fun n => coff_in_poly (y1-(fun x => ∑' (i : ℕ), multichoose' x i • a i)) n)=0 :=by
      rw[th1]
      have:(fun n => coff_in_poly (fun (x:ℤ_[p]) => ∑' (i : ℕ), multichoose' x i • a i) n)
        = a :=by sorry
      rw[this]
      rw[sy]
      simp
    have:y1-(fun x => ∑' (i : ℕ), multichoose' x i • a i)=0 :=by
      have fq1: Continuous (y1-(fun x => ∑' (i : ℕ), multichoose' x i • a i)) :=by
        have s1: Continuous y1 :=by exact y2
        have s2:Continuous (fun (x:ℤ_[p]) => ∑' (i : ℕ), multichoose' x i • a i) :=by
          exact is_continue_for_summable_multchoose p ha
        have dm: Continuous (fun (x:ℤ_[p]) => y1 x- ∑' (i : ℕ), multichoose' x i • a i) :=by
          exact Continuous.sub y2 s2
        have:(fun (x:ℤ_[p]) => y1 x- ∑' (i : ℕ), multichoose' x i • a i)=
          y1-(fun x => ∑' (i : ℕ), multichoose' x i • a i) :=by rfl
        rw[this] at dm
        exact dm
      rw[gmui (y1-(fun x => ∑' (i : ℕ), multichoose' x i • a i)) fq1] at th2
      exact th2
    rw[Eq.symm (sub_add_cancel y1 fun x => ∑' (i : ℕ), multichoose' x i • a i),this]
    simp
  exact ContinuousMap.ext (congrFun this)
lemma existance (f:ℤ_[p]→ ℚ_[p])(hs:Continuous f): ∃   a : ℕ → ℚ_[p] ,
   f  =(fun x =>∑' i : ℕ, (multichoose'  x  i  )• a i)∧ Summable a:=by

   use (fun_c_f_to_bound_a ⟨f,hs⟩).1
   constructor
   · have j1: Continuous (fun (x:ℤ_[p]) => ∑' (i : ℕ), multichoose' x i • (fun_c_f_to_bound_a ⟨f, hs⟩).1 i):=by
      refine is_continue_for_summable_multchoose p (fun_c_f_to_bound_a ⟨f, hs⟩).2
     have j2: (fun_c_f_to_bound_a ⟨f,hs⟩)=(fun_c_f_to_bound_a ⟨(fun (x:ℤ_[p]) =>
        ∑' (i : ℕ), multichoose' x i •
        (fun_c_f_to_bound_a ⟨f, hs⟩).1 i),j1⟩):=by sorry
     have:∃! a, fun_c_f_to_bound_a  a =  (fun_c_f_to_bound_a ⟨f,hs⟩) :=by
      refine
        Function.Bijective.existsUnique (bij) (fun_c_f_to_bound_a ⟨f, hs⟩)
     rcases this with ⟨⟨r1,r2⟩,⟨d1,d2⟩⟩
     have z1: (fun a => fun_c_f_to_bound_a a = fun_c_f_to_bound_a ⟨f, hs⟩) ⟨f, hs⟩ :=by
       exact rfl
     have ds1: f =r1:=by
       rcases (d2 ⟨f,hs⟩ z1)
       simp
     have ds2: (fun (x:ℤ_[p]) =>∑' (i : ℕ), multichoose' x i •
          (fun_c_f_to_bound_a ⟨f, hs⟩).1 i)=r1:=by
       have:  (fun a => fun_c_f_to_bound_a a = fun_c_f_to_bound_a ⟨f, hs⟩)
        ⟨fun x => ∑' (i : ℕ), multichoose' x i • (fun_c_f_to_bound_a ⟨f, hs⟩).1 i, j1⟩
         :=by
          dsimp
          exact id (Eq.symm j2)
       rcases  (d2 ⟨(fun (x:ℤ_[p]) =>∑' (i : ℕ), multichoose' x i •
           (fun_c_f_to_bound_a ⟨f, hs⟩).1 i),j1⟩ this)
       simp
     rw[ds2]
     exact ds1
   · exact (fun_c_f_to_bound_a ⟨f,hs⟩).2


end bijective

section the_measure_of_f

variable {p : ℕ} [sh:Fact (Nat.Prime p)]

lemma discrete_value1 (f: C(ℤ_[p],ℚ_[p])):∃ a:ℤ_[p], ‖f a‖ =‖f‖ :=by
   have:‖f‖=0∨ ‖f‖> 0 :=by
    sorry
   rcases this with j1| j2
   · use 1
     rw[j1]
     have e1: ‖f 1‖ ≤ ‖f‖ :=by exact ContinuousMap.norm_coe_le_norm f 1
     rw[j1] at e1
     have e2:‖f 1‖≥ 0 :=by exact norm_nonneg (f 1)
     sorry

   rw[ContinuousMap.norm_eq_iSup_norm f]
   by_contra qj
   have k1: ∀ a: ℤ_[p] ,‖f a‖ < iSup (fun a => ‖f a‖ ) :=by
      intro a
      have:‖f a‖≤ iSup (fun a => ‖f a‖ ) :=by
        have:‖f a‖ ≤ ‖f‖  :=by exact ContinuousMap.norm_coe_le_norm f a
        rw[ContinuousMap.norm_eq_iSup_norm f] at this
        exact this
      rw[le_iff_eq_or_lt] at this
      rcases this with d1|d2
      have:∃ a:ℤ_[p], ‖f a‖ =⨆ x, ‖f x‖ :=by
        use a
      exact False.elim (qj this)
      exact d2
   have mms: (p:ℝ)^(Int.clog p ‖f‖ -1)<‖f‖  :=by
      rw[Int.zpow_lt_iff_lt_clog]
      exact _root_.sub_one_lt (Int.clog p ‖f‖)
      · sorry
      · exact j2
   rw[ContinuousMap.norm_eq_iSup_norm f] at mms
   have:  ∃ i:ℤ_[p], (p:ℝ)^(Int.clog p ‖f‖ -1) < ‖f i‖  :=by
     sorry
   rcases this with ⟨i,slk⟩

   have grg: ‖f i‖ =↑p ^ (-Padic.valuation (f i)) :=by
     refine Padic.norm_eq_pow_val ?_
     by_contra sm
     rw[sm] at slk
     simp at slk
     have: (p:ℝ)^ (Int.clog p ‖f‖ - 1) ≥  0 :=by
      refine zpow_nonneg ( cast_nonneg' p) (Int.clog p ‖f‖ - 1)
     have:¬ (p:ℝ)^ (Int.clog p ‖f‖ - 1) <  0 :=by exact not_lt.mpr this
     exact this slk
   rw[grg] at slk
   have: (Int.clog p ‖f‖ - 1) < (-(f i).valuation) :=by
      have:(p:ℝ)>1 :=by sorry
      exact (zpow_lt_zpow_iff_right₀ this).mp slk
   have:Int.clog p ‖f‖≤  (-(f i).valuation) :=by exact Int.le_of_sub_one_lt this
   have jrj: (p:ℝ)^ (Int.clog p ‖f‖ ) ≤ (p:ℝ)^ (-(f i).valuation) :=by
      have ko:(p:ℝ)>1 :=by sorry
      exact (zpow_le_zpow_iff_right₀ ko).mpr this
   rw[← grg] at jrj
   have: ‖f‖ ≤ (p:ℝ)^ (Int.clog p ‖f‖ ) :=by
      refine Int.self_le_zpow_clog ?hb ‖f‖
   have:‖f‖≤  ‖f i‖  :=by
      sorry
   have:¬ ‖f i‖ <‖f‖:=by exact not_lt.mpr this
   have j2: ‖f i‖ <‖f‖  :=by
     rw[ContinuousMap.norm_eq_iSup_norm f]
     exact k1 i
   exact this j2





end the_measure_of_f
section theorem_1_3_2

variable {p : ℕ} [sh:Fact (Nat.Prime p)] (f : C(ℤ_[p],ℚ_[p]))


theorem mahler₁ : Filter.Tendsto (fun (n : ℕ) => ‖(coff_in_poly f n)‖) Filter.atTop (nhds 0) := sorry



theorem mahler₂ : ∀ x : ℤ_[p], f x = ∑' (n : ℕ), (multichoose' x n)•(coff_in_poly f n) := by
  have : ∃   a : ℕ → ℚ_[p] ,(∀ x : ℤ_[p] , f x =∑' i : ℕ, (multichoose'  x  i  )• a i) ∧ Summable a:=by
     rcases (existance f f.2) with ⟨a,⟨c1,c2⟩⟩
     use a
     constructor
     exact fun x => congrFun c1 x
     exact c2
  rcases this with ⟨a,⟨hs1,hs2⟩⟩
  intro x
  have: ∀ i : ℕ ,    (coff_in_poly f i)=a i :=by
    intro s
    have sdq1 : discrete_derivatives f s 0=  ∑' (i:ℕ ), (multichoose' (0:ℤ_[p])  i )•a (s+i)   :=by sorry
    have sdq2 : ∑' (i : ℕ), multichoose' (0:ℤ_[p]) i • a (s+i)= multichoose' (0:ℤ_[p]) 0 • a s + ∑' (i : ℕ), multichoose' (0:ℤ_[p]) (i+1) •
   a (s+i+1):=by
      have ds:Summable (fun (i:ℕ ) =>( multichoose' (0:ℤ_[p]) i • a (s+i))):=by
        exact summable_th3  a (fun x =>multichoose' (0:ℤ_[p]) x ) hs2 s
      exact tsum_eq_zero_add ds
    have sdq4 : ∑' (i : ℕ), multichoose' (0:ℤ_[p]) (i+1) • a (s+i+1)=0 :=by
      have:  ∑' (i : ℕ), multichoose' (0:ℤ_[p]) (i+1) • a (s+i+1)=∑' (i : ℕ), 0 :=by
        refine tsum_congr ?hfg
        intro b
        rw[zero b]
        simp
      rw[this]
      simp
    unfold coff_in_poly

    rw[sdq1,sdq2,sdq4]
    unfold   multichoose'
    simp
  rw[hs1]
  rw[tsum_congr]
  intro b
  rw[this]

theorem mahler₃ : ‖f‖ = iInf (fun (n : ℕ) => ‖(coff_in_poly f n)‖) := sorry

end theorem_1_3_2
