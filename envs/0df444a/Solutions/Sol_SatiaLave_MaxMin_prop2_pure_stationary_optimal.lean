-- Prove2me | solution 1 for SatiaLave.MaxMin.prop2_pure_stationary_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:51:02.63299+00:00
-- url     : https://prove2.me/submissions/6ec6ce3f-aad4-4dcd-ad12-cc4e2ec2af99

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Eq4

set_option autoImplicit false

namespace SatiaLaveP2

open SatiaLave.MaxMin Finset MeasureTheory
open scoped Matrix

lemma key {S : Type*} [Fintype S] (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1) (P : S → S → ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1)
    (d : S → ℝ) (hd : ∀ i, d i ≤ β * ∑ j, P i j * d j) : ∀ i, d i ≤ 0 := by
  intro i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ d ⟨i, Finset.mem_univ _⟩
  have h1 : ∑ j, P i0 j * d j ≤ d i0 := by
    calc ∑ j, P i0 j * d j ≤ ∑ j, P i0 j * d i0 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi0 j (mem_univ _)) (hP0 _ _)
      _ = d i0 := by rw [← Finset.sum_mul, hP1, one_mul]
  have h2 : d i0 ≤ β * d i0 := (hd i0).trans (mul_le_mul_of_nonneg_left h1 hβ0)
  have h3 : d i0 ≤ 0 := by nlinarith
  exact (hi0 i (mem_univ _)).trans h3

lemma cmp {S : Type*} [Fintype S] (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1) (P : S → S → ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (a : S → S → ℝ) (x y : S → ℝ)
    (hy : ∀ i, y i ≤ ∑ j, P i j * (a i j + β * y j))
    (hx : ∀ i, ∑ j, P i j * (a i j + β * x j) ≤ x i) : ∀ i, y i ≤ x i := by
  have := key β hβ0 hβ P hP0 hP1 (fun i => y i - x i) (by
    intro i
    have e : ∑ j, P i j * (a i j + β * y j) - ∑ j, P i j * (a i j + β * x j)
        = β * ∑ j, P i j * (y j - x j) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have := hy i; have := hx i
    show y i - x i ≤ β * ∑ j, P i j * (y j - x j)
    linarith)
  intro i
  exact sub_nonpos.1 (this i)

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}

/-- the one-step value of a row `p` -/
def g (M : UncertainMDP S D) (v : S → ℝ) (j : S) (k : D j) (p : S → ℝ) : ℝ :=
  ∑ l, p l * (M.r j k l + M.β * v l)

lemma g_cont (M : UncertainMDP S D) (v : S → ℝ) (j : S) (k : D j) : Continuous (g M v j k) := by
  unfold g; fun_prop

lemma U_compact (M : UncertainMDP S D) (j : S) (k : D j) : IsCompact (M.U j k) :=
  (isCompact_stdSimplex ℝ S).of_isClosed_subset (M.U_closed j k) (M.U_subset j k)

noncomputable def m (M : UncertainMDP S D) (v : S → ℝ) (j : S) (k : D j) : ℝ :=
  ⨅ p : M.U j k, g M v j k p

lemma exists_min (M : UncertainMDP S D) (v : S → ℝ) (j : S) (k : D j) :
    ∃ p ∈ M.U j k, m M v j k = g M v j k p ∧ ∀ q ∈ M.U j k, g M v j k p ≤ g M v j k q := by
  obtain ⟨p, hp, hmin⟩ := (U_compact M j k).exists_isMinOn (M.U_nonempty j k)
    (g_cont M v j k).continuousOn
  refine ⟨p, hp, ?_, fun q hq => hmin hq⟩
  haveI : Nonempty (M.U j k) := ⟨⟨p, hp⟩⟩
  apply le_antisymm
  · have hb : BddBelow (Set.range fun q : M.U j k => g M v j k q) :=
      ⟨g M v j k p, by rintro _ ⟨q, rfl⟩; exact hmin q.2⟩
    exact ciInf_le hb ⟨p, hp⟩
  · exact le_ciInf fun q : M.U j k => (hmin q.2 : g M v j k p ≤ g M v j k q)

lemma m_le (M : UncertainMDP S D) (v : S → ℝ) (j : S) (k : D j) (q : S → ℝ) (hq : q ∈ M.U j k) :
    m M v j k ≤ g M v j k q := by
  obtain ⟨p, -, hm, hmin⟩ := exists_min M v j k
  rw [hm]; exact hmin q hq

variable [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

noncomputable def T (M : UncertainMDP S D) (v : S → ℝ) (j : S) : ℝ :=
  (Finset.univ : Finset (D j)).sup' Finset.univ_nonempty (fun k => m M v j k)

lemma inner_eq (M : UncertainMDP S D) (v : S → ℝ) (j : S) (k : D j) :
    (⨅ α : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1},
      ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(α.1 : Measure (S → ℝ))) = m M v j k := by
  obtain ⟨p0, hp0U, hm, hmin⟩ := exists_min M v j k
  have hmeas : MeasurableSet (M.U j k) := (M.U_closed j k).measurableSet
  let α0 : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1} :=
    ⟨⟨Measure.dirac p0, inferInstance⟩, by
      show Measure.dirac p0 (M.U j k) = 1
      exact Measure.dirac_apply_of_mem hp0U⟩
  have hlow : ∀ α : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1},
      m M v j k ≤ ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(α.1 : Measure (S → ℝ)) := by
    intro α
    have hae : ∀ᵐ p ∂(α.1 : Measure (S → ℝ)), p ∈ M.U j k := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hmeas).2 α.2
    obtain ⟨C, hC⟩ := (U_compact M j k).exists_bound_of_continuousOn
      (g_cont M v j k).continuousOn
    have hint : Integrable (g M v j k) (α.1 : Measure (S → ℝ)) :=
      Integrable.of_bound (g_cont M v j k).aestronglyMeasurable C
        (hae.mono fun p hp => hC p hp)
    calc m M v j k = ∫ _p, m M v j k ∂(α.1 : Measure (S → ℝ)) := by simp
      _ ≤ ∫ p, g M v j k p ∂(α.1 : Measure (S → ℝ)) :=
          integral_mono_ae (integrable_const _) hint
            (hae.mono fun p hp => hm ▸ hmin p hp)
      _ = _ := rfl
  haveI : Nonempty {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1} :=
    ⟨α0⟩
  apply le_antisymm
  · refine (ciInf_le ⟨m M v j k, by rintro _ ⟨α, rfl⟩; exact hlow α⟩ α0).trans ?_
    show ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(Measure.dirac p0) ≤ m M v j k
    rw [integral_dirac, hm]
    rfl
  · exact le_ciInf hlow

lemma eq4_eq (M : UncertainMDP S D) (v : S → ℝ) (j : S) : eq4Op M v j = T M v j := by
  classical
  unfold eq4Op
  simp_rw [inner_eq]
  obtain ⟨K, -, hK⟩ := Finset.exists_max_image (Finset.univ : Finset (D j)) (fun k => m M v j k)
    Finset.univ_nonempty
  have hT : T M v j = m M v j K :=
    le_antisymm (Finset.sup'_le _ _ fun k _ => hK k (mem_univ _))
      (Finset.le_sup' (fun k => m M v j k) (mem_univ K))
  have hup : ∀ τ : stdSimplex ℝ (D j), ∑ k, (τ : D j → ℝ) k * m M v j k ≤ m M v j K := by
    intro τ
    calc ∑ k, (τ : D j → ℝ) k * m M v j k ≤ ∑ k, (τ : D j → ℝ) k * m M v j K :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hK k (mem_univ _)) (τ.2.1 k)
      _ = m M v j K := by
          have h2 : ∑ k, (τ : D j → ℝ) k = 1 := τ.2.2
          rw [← Finset.sum_mul, h2, one_mul]
  let τ0 : stdSimplex ℝ (D j) := ⟨Pi.single K 1, single_mem_stdSimplex ℝ K⟩
  haveI : Nonempty (stdSimplex ℝ (D j)) := ⟨τ0⟩
  rw [hT]
  apply le_antisymm (ciSup_le hup)
  refine le_trans ?_ (le_ciSup ⟨m M v j K, by rintro _ ⟨τ, rfl⟩; exact hup τ⟩ τ0)
  show m M v j K ≤ ∑ k, (Pi.single K 1 : D j → ℝ) k * m M v j k
  simp [Pi.single_apply]

lemma T_le (M : UncertainMDP S D) (v w : S → ℝ) (j : S) :
    T M v j ≤ T M w j + M.β * dist v w := by
  unfold T
  refine Finset.sup'_le _ _ fun k _ => ?_
  obtain ⟨p, hp, hm, -⟩ := exists_min M w j k
  have h1 : m M v j k ≤ g M v j k p := m_le M v j k p hp
  have h2 : g M v j k p - g M w j k p ≤ M.β * dist v w := by
    have e : g M v j k p - g M w j k p = M.β * ∑ l, p l * (v l - w l) := by
      unfold g
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ M.β_nonneg
    have hs := M.U_subset j k hp
    calc ∑ l, p l * (v l - w l) ≤ ∑ l, p l * dist v w := by
          refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hs.1 l)
          exact (le_abs_self _).trans ((Real.dist_eq _ _).symm ▸ dist_le_pi_dist v w l)
      _ = dist v w := by rw [← Finset.sum_mul, hs.2, one_mul]
  have h3 : m M w j k ≤ (Finset.univ : Finset (D j)).sup' Finset.univ_nonempty
      (fun k => m M w j k) := Finset.le_sup' (fun k => m M w j k) (mem_univ k)
  linarith

lemma exists_fixed (M : UncertainMDP S D) : ∃ v, T M v = v := by
  have hK : ContractingWith (Real.toNNReal M.β) (T M) := by
    refine ⟨Real.toNNReal_lt_one.2 M.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    rw [Real.coe_toNNReal _ M.β_nonneg]
    refine (dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)).2 fun j => ?_
    rw [Real.dist_eq, abs_sub_le_iff]
    have := T_le M v w j
    have := T_le M w v j
    rw [dist_comm w v] at this
    constructor <;> linarith
  exact ⟨_, ContractingWith.fixedPoint_isFixedPt hK⟩

instance sel_nonempty (M : UncertainMDP S D) : Nonempty (Sel M) :=
  ⟨⟨fun i k => (M.U_nonempty i k).some, fun i k => (M.U_nonempty i k).some_mem⟩⟩

lemma row_nonneg (M : UncertainMDP S D) (P : Sel M) (i : S) (k : D i) (j : S) :
    0 ≤ P.1 i k j := (M.U_subset i k (P.2 i k)).1 j

lemma row_sum (M : UncertainMDP S D) (P : Sel M) (i : S) (k : D i) :
    ∑ j, P.1 i k j = 1 := (M.U_subset i k (P.2 i k)).2

lemma pv_eq (M : UncertainMDP S D) (B : Policy S D) (P : Sel M) (i : S) :
    presentValue M B P i
      = ∑ j, P.1 i (B i) j * (M.r i (B i) j + M.β * presentValue M B P j) := by
  set A : Matrix S S ℝ := 1 - M.β • transMat M B P with hA
  have hmv : ∀ y : S → ℝ, ∀ i, (A *ᵥ y) i = y i - M.β * ∑ j, P.1 i (B i) j * y j := by
    intro y i
    simp [hA, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, transMat,
      Matrix.one_apply]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
  have hinj : Function.Injective A.mulVec := by
    intro y z hyz
    have hd : ∀ i, y i - z i = M.β * ∑ j, P.1 i (B i) j * (y j - z j) := by
      intro i
      have := congrFun hyz i
      rw [hmv, hmv] at this
      have e : ∑ j, P.1 i (B i) j * (y j - z j)
          = ∑ j, P.1 i (B i) j * y j - ∑ j, P.1 i (B i) j * z j := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]; linarith
    have h1 := key M.β M.β_nonneg M.β_lt_one (fun i j => P.1 i (B i) j)
      (fun i j => row_nonneg M P i (B i) j) (fun i => row_sum M P i (B i))
      (fun i => y i - z i) (fun i => (hd i).le)
    have h2 := key M.β M.β_nonneg M.β_lt_one (fun i j => P.1 i (B i) j)
      (fun i j => row_nonneg M P i (B i) j) (fun i => row_sum M P i (B i))
      (fun i => z i - y i) (fun i => by
        have := hd i
        have e : ∑ j, P.1 i (B i) j * (z j - y j) = - ∑ j, P.1 i (B i) j * (y j - z j) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [e]; linarith)
    funext i
    linarith [sub_nonpos.1 (h1 i), sub_nonpos.1 (h2 i)]
  have hU : IsUnit A := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hU
  have hx : A *ᵥ presentValue M B P = rewardVec M B P := by
    unfold presentValue
    rw [← hA, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have := congrFun hx i
  rw [hmv] at this
  unfold rewardVec at this
  have e : ∑ j, P.1 i (B i) j * (M.r i (B i) j + M.β * presentValue M B P j)
      = ∑ j, P.1 i (B i) j * M.r i (B i) j + M.β * ∑ j, P.1 i (B i) j * presentValue M B P j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]; linarith

lemma pv_bdd (M : UncertainMDP S D) (B : Policy S D) (i : S) :
    BddBelow (Set.range fun P : Sel M => presentValue M B P i) := by
  haveI : Nonempty S := ⟨i⟩
  obtain ⟨c0, hc0⟩ := Finite.exists_le (fun ij : S × S => -M.r ij.1 (B ij.1) ij.2)
  set c1 := min (-c0) 0
  set c := c1 / (1 - M.β)
  have hβ : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hc : c = c1 + M.β * c := by
    have : c * (1 - M.β) = c1 := div_mul_cancel₀ _ hβ.ne'
    linarith
  refine ⟨c, ?_⟩
  rintro _ ⟨P, rfl⟩
  refine cmp M.β M.β_nonneg M.β_lt_one (fun i j => P.1 i (B i) j)
    (fun i j => row_nonneg M P i (B i) j) (fun i => row_sum M P i (B i))
    (fun i j => M.r i (B i) j) (presentValue M B P) (fun _ => c) ?_ ?_ i
  · intro i
    calc c = ∑ j, P.1 i (B i) j * (c1 + M.β * c) := by
          rw [← Finset.sum_mul, row_sum, one_mul, ← hc]
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (by have := hc0 (i, j); simp only at this ⊢; linarith [min_le_left (-c0) 0])
          (row_nonneg M P i (B i) j)
  · intro i; exact (pv_eq M B P i).symm.le

/-- argmax policy for `v` -/
noncomputable def Aopt (M : UncertainMDP S D) (v : S → ℝ) : Policy S D := fun i =>
  (Finset.exists_max_image (Finset.univ : Finset (D i)) (fun k => m M v i k)
    Finset.univ_nonempty).choose

lemma Aopt_spec (M : UncertainMDP S D) (v : S → ℝ) (i : S) : m M v i (Aopt M v i) = T M v i := by
  have h := (Finset.exists_max_image (Finset.univ : Finset (D i)) (fun k => m M v i k)
    Finset.univ_nonempty).choose_spec
  exact le_antisymm (Finset.le_sup' (fun k => m M v i k) (mem_univ _))
    (Finset.sup'_le _ _ fun k _ => h.2 k (mem_univ _))

/-- argmin selection for `v` -/
noncomputable def Pmin (M : UncertainMDP S D) (v : S → ℝ) : Sel M :=
  ⟨fun i k => (exists_min M v i k).choose, fun i k => (exists_min M v i k).choose_spec.1⟩

lemma upper (M : UncertainMDP S D) (v : S → ℝ) (hv : T M v = v) (B : Policy S D) (i : S) :
    robustValue M B i ≤ v i := by
  refine (ciInf_le (pv_bdd M B i) (Pmin M v)).trans ?_
  refine cmp M.β M.β_nonneg M.β_lt_one (fun i j => (Pmin M v).1 i (B i) j)
    (fun i j => row_nonneg M _ i (B i) j) (fun i => row_sum M _ i (B i))
    (fun i j => M.r i (B i) j) v (presentValue M B (Pmin M v)) ?_ ?_ i
  · intro i; exact (pv_eq M B _ i).le
  · intro i
    have h := (exists_min M v i (B i)).choose_spec.2.1
    have h2 : m M v i (B i) ≤ T M v i := Finset.le_sup' (fun k => m M v i k) (mem_univ _)
    rw [hv] at h2
    show g M v i (B i) (exists_min M v i (B i)).choose ≤ v i
    rw [← h]; exact h2

lemma lower (M : UncertainMDP S D) (v : S → ℝ) (hv : T M v = v) (i : S) :
    v i ≤ robustValue M (Aopt M v) i := by
  refine le_ciInf fun P => ?_
  refine cmp M.β M.β_nonneg M.β_lt_one (fun i j => P.1 i (Aopt M v i) j)
    (fun i j => row_nonneg M _ i _ j) (fun i => row_sum M _ i _)
    (fun i j => M.r i (Aopt M v i) j) (presentValue M (Aopt M v) P) v ?_ ?_ i
  · intro i
    have := m_le M v i (Aopt M v i) (P.1 i (Aopt M v i)) (P.2 i _)
    rw [Aopt_spec, hv] at this
    exact this
  · intro i; exact (pv_eq M _ P i).symm.le

lemma robust_eq (M : UncertainMDP S D) (v : S → ℝ) (hv : T M v = v) (i : S) :
    robustValue M (Aopt M v) i = v i :=
  le_antisymm (upper M v hv _ i) (lower M v hv i)

end SatiaLaveP2

open SatiaLave.MaxMin in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    ∃ A : Policy S D, (∀ v : S → ℝ, (∀ j, v j = eq4Op M v j) → ∀ j, robustValue M A j = v j) ∧
      IsMaxMinOptimal M A := by
  obtain ⟨vs, hvs⟩ := SatiaLaveP2.exists_fixed M
  refine ⟨SatiaLaveP2.Aopt M vs, ?_, ?_⟩
  · intro v hv j
    have hT : SatiaLaveP2.T M v = v := funext fun j => by
      rw [← SatiaLaveP2.eq4_eq]; exact (hv j).symm
    have e : vs = v := funext fun i => le_antisymm
      ((SatiaLaveP2.robust_eq M vs hvs i).symm.le.trans (SatiaLaveP2.upper M v hT _ i))
      ((SatiaLaveP2.robust_eq M v hT i).symm.le.trans (SatiaLaveP2.upper M vs hvs _ i))
    rw [SatiaLaveP2.robust_eq M vs hvs j, e]
  · intro i
    unfold maxMinValue
    apply le_antisymm
    · exact Finset.le_sup' (fun A => robustValue M A i) (Finset.mem_univ _)
    · refine Finset.sup'_le _ _ fun B _ => ?_
      rw [SatiaLaveP2.robust_eq M vs hvs i]
      exact SatiaLaveP2.upper M vs hvs B i
