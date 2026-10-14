-- Prove2me | solution 1 for TPG.variance_sum_window_le
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:40:11.495974+00:00
-- url     : https://prove2.me/submissions/d7fd7314-5458-42be-a31c-efe0b1923074

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference
import Theorems.Thm_TPG_lemma_1_covariance_inequality
import Theorems.Thm_TPG_lemma_2_alpha_mixing
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_VW_Var

/-- Every window sigma-algebra is contained in the product sigma-algebra on trajectories. -/
lemma sigmaWindow_le {S : Type} [MeasurableSpace S] (T a b : ℕ) :
    sigmaWindow (S := S) T a b ≤ (inferInstance : MeasurableSpace (Traj S T)) := by
  unfold sigmaWindow
  exact iSup₂_le fun t _ => (measurable_pi_apply t).comap_le

/-- Window sigma-algebras are monotone in the time window. -/
lemma sigmaWindow_mono {S : Type} [MeasurableSpace S] (T : ℕ) {a b a' b' : ℕ}
    (ha : a' ≤ a) (hb : b ≤ b') :
    sigmaWindow (S := S) T a b ≤ sigmaWindow T a' b' := by
  unfold sigmaWindow
  exact iSup₂_le fun t ht => le_iSup₂_of_le t ⟨ha.trans ht.1, ht.2.trans hb⟩ le_rfl

/-- Two random variables bounded by `K` have covariance at most `K ^ 2` in absolute value. -/
lemma abs_cov_le_sq {Ω : Type} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (K : ℝ)
    (hXK : ∀ ω, |X ω| ≤ K) (hYK : ∀ ω, |Y ω| ≤ K) :
    |cov[X, Y; μ]| ≤ K ^ 2 := by
  have hXm : MemLp X 2 μ :=
    MemLp.of_bound hX.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hXK ω)
  have hYm : MemLp Y 2 μ :=
    MemLp.of_bound hY.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hYK ω)
  have hvX : Var[X; μ] ≤ K ^ 2 := by
    have h := variance_le_sq_of_bounded (μ := μ) (a := -K) (b := K) (X := X)
      (Filter.Eventually.of_forall fun ω => abs_le.mp (hXK ω)) hX.aemeasurable
    calc Var[X; μ] ≤ ((K - -K) / 2) ^ 2 := h
      _ = K ^ 2 := by ring
  have hvY : Var[Y; μ] ≤ K ^ 2 := by
    have h := variance_le_sq_of_bounded (μ := μ) (a := -K) (b := K) (X := Y)
      (Filter.Eventually.of_forall fun ω => abs_le.mp (hYK ω)) hY.aemeasurable
    calc Var[Y; μ] ≤ ((K - -K) / 2) ^ 2 := h
      _ = K ^ 2 := by ring
  have h1 := variance_add hXm hYm
  have h2 := variance_sub hXm hYm
  have h3 := variance_nonneg (X + Y) μ
  have h4 := variance_nonneg (X - Y) μ
  rw [abs_le]
  constructor <;> linarith

/-- The number of indices within distance `w + 1` of `i` is at most `2 w + 3`. -/
lemma sum_near_le (i w T : ℕ) :
    ∑ j ∈ Finset.range T,
        (if j ∈ Finset.Icc (i - (w + 1)) (i + (w + 1)) then (1 : ℝ) else 0)
      ≤ 2 * (w : ℝ) + 3 := by
  rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : (Finset.range T ∩ Finset.Icc (i - (w + 1)) (i + (w + 1))).card ≤ 2 * w + 3 := by
    calc (Finset.range T ∩ Finset.Icc (i - (w + 1)) (i + (w + 1))).card
        ≤ (Finset.Icc (i - (w + 1)) (i + (w + 1))).card :=
          Finset.card_le_card Finset.inter_subset_right
      _ = i + (w + 1) + 1 - (i - (w + 1)) := Nat.card_Icc _ _
      _ ≤ 2 * w + 3 := by omega
  exact_mod_cast h1

/-- A shifted geometric sum is bounded by the full geometric series. -/
lemma sum_far_le (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (a T : ℕ) :
    ∑ j ∈ Finset.range T, (if a ≤ j then 4 * γ ^ (j - a) else 0) ≤ 4 / (1 - γ) := by
  have hnn : ∀ j : ℕ, 0 ≤ (if a ≤ j then 4 * γ ^ (j - a) else 0 : ℝ) := by
    intro j
    split_ifs
    · positivity
    · exact le_rfl
  calc ∑ j ∈ Finset.range T, (if a ≤ j then 4 * γ ^ (j - a) else 0)
      ≤ ∑ j ∈ Finset.range (a + T), (if a ≤ j then 4 * γ ^ (j - a) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_left T a))
          (fun j _ _ => hnn j)
    _ = ∑ k ∈ Finset.range T, 4 * γ ^ k := by
        rw [Finset.sum_range_add, Finset.sum_eq_zero, zero_add]
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [if_pos (Nat.le_add_right a k), Nat.add_sub_cancel_left]
        · intro j hj
          rw [if_neg (Nat.not_le.mpr (Finset.mem_range.mp hj))]
    _ = 4 * ∑ k ∈ Finset.range T, γ ^ k := by rw [Finset.mul_sum]
    _ ≤ 4 * (1 - γ)⁻¹ := by
        have hpow : 0 ≤ γ ^ T := by positivity
        have hinv : 0 < (1 - γ)⁻¹ := inv_pos.mpr (by linarith)
        have h : ∑ k ∈ Finset.range T, γ ^ k ≤ (1 - γ)⁻¹ := by
          rw [geom_sum_eq hγ1.ne, ← neg_sub 1 γ, ← neg_sub 1 (γ ^ T), neg_div_neg_eq,
            div_eq_mul_inv]
          have := mul_nonneg hpow hinv.le
          linarith
        linarith
    _ = 4 / (1 - γ) := by rw [div_eq_mul_inv]

end TPG_VW_Var

open TPG_VW_Var in
theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T w : ℕ) (θ γ M K : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M)
    (U : ℕ → Traj S T → ℝ)
    (hU : ∀ j : ℕ, Measurable[sigmaWindow T (j - w) j] (U j))
    (hK : ∀ (j : ℕ) (ω : Traj S T), |U j ω| ≤ K) :
    variance (fun ω : Traj S T => ∑ j ∈ Finset.range T, U j ω) (E.expLaw T θ)
      ≤ (T : ℝ) * K ^ 2 * (2 * (w : ℝ) + 3 + 8 / (1 - γ)) := by
  classical
  have hprob : IsProbabilityMeasure (E.expLaw T θ) :=
    isProbabilityMeasure_trajLaw E T (fun _ => θ) (fun _ => ⟨hθ0.le, hθ1.le⟩)
  have hUm : ∀ j, Measurable (U j) := fun j => (hU j).mono (sigmaWindow_le T _ _) le_rfl
  have hL2 : ∀ j, MemLp (U j) 2 (E.expLaw T θ) := fun j =>
    MemLp.of_bound (hUm j).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hK j ω)
  -- every covariance is at most `K ^ 2`
  have hnear : ∀ i j, |cov[U i, U j; E.expLaw T θ]| ≤ K ^ 2 := fun i j =>
    abs_cov_le_sq (E.expLaw T θ) (U i) (U j) (hUm i) (hUm j) K (hK i) (hK j)
  -- covariances of well separated terms decay geometrically
  have hfar : ∀ i j, i + w + 2 ≤ j → j < T →
      |cov[U i, U j; E.expLaw T θ]| ≤ K ^ 2 * (4 * γ ^ (j - (i + w + 2))) := by
    intro i j hij hjT
    obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hsh : i + h + 1 < T := by omega
    have hXi : Measurable[sigmaWindow T 0 i] (U i) :=
      (hU i).mono (sigmaWindow_mono T (Nat.zero_le _) le_rfl) le_rfl
    have hYj : Measurable[sigmaWindow T (i + h + 1) T] (U (i + w + 2 + h)) :=
      (hU _).mono (sigmaWindow_mono T (by omega) (by omega)) le_rfl
    have hcov := lemma_1_covariance_inequality (E.expLaw T θ)
      (sigmaWindow T 0 i) (sigmaWindow T (i + h + 1) T)
      (sigmaWindow_le T _ _) (sigmaWindow_le T _ _) (U i) (U (i + w + 2 + h)) hXi hYj K K (γ ^ h)
      (Filter.Eventually.of_forall (hK i)) (Filter.Eventually.of_forall (hK _))
      (fun A B hA hB =>
        lemma_2_alpha_mixing E T θ γ M hθ0 hθ1 hγ0 hγ1 hmix hM i h hsh A B hA hB)
    have e : i + w + 2 + h - (i + w + 2) = h := by omega
    rw [e]
    linarith
  -- comparison weights
  set near : ℕ → ℕ → ℝ := fun i j =>
    if j ∈ Finset.Icc (i - (w + 1)) (i + (w + 1)) then (1 : ℝ) else 0 with hnear_def
  set far : ℕ → ℕ → ℝ := fun i j =>
    if i + w + 2 ≤ j then 4 * γ ^ (j - (i + w + 2)) else 0 with hfar_def
  have hnear0 : ∀ i j, 0 ≤ near i j := by
    intro i j
    simp only [hnear_def]
    split_ifs <;> norm_num
  have hfar0 : ∀ i j, 0 ≤ far i j := by
    intro i j
    simp only [hfar_def]
    split_ifs
    · positivity
    · exact le_rfl
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hpair : ∀ i ∈ Finset.range T, ∀ j ∈ Finset.range T,
      cov[U i, U j; E.expLaw T θ] ≤ K ^ 2 * (near i j + far i j + far j i) := by
    intro i hi j hj
    rw [Finset.mem_range] at hi hj
    have n1 := mul_nonneg hK2 (hnear0 i j)
    have n2 := mul_nonneg hK2 (hfar0 i j)
    have n3 := mul_nonneg hK2 (hfar0 j i)
    rw [mul_add, mul_add]
    by_cases h1 : i + w + 2 ≤ j
    · have hb := hfar i j h1 hj
      have e : far i j = 4 * γ ^ (j - (i + w + 2)) := by
        simp only [hfar_def]; rw [if_pos h1]
      rw [← e] at hb
      have := le_abs_self (cov[U i, U j; E.expLaw T θ])
      linarith
    · by_cases h2 : j + w + 2 ≤ i
      · have hb := hfar j i h2 hi
        have e : far j i = 4 * γ ^ (i - (j + w + 2)) := by
          simp only [hfar_def]; rw [if_pos h2]
        rw [← e, covariance_comm] at hb
        have := le_abs_self (cov[U i, U j; E.expLaw T θ])
        linarith
      · have hmem : j ∈ Finset.Icc (i - (w + 1)) (i + (w + 1)) := by
          rw [Finset.mem_Icc]; omega
        have e : near i j = 1 := by
          simp only [hnear_def]; rw [if_pos hmem]
        have hb := hnear i j
        have := le_abs_self (cov[U i, U j; E.expLaw T θ])
        rw [e, mul_one]
        linarith
  have hsum_near : ∀ i, ∑ j ∈ Finset.range T, near i j ≤ 2 * (w : ℝ) + 3 := fun i =>
    sum_near_le i w T
  have hsum_far : ∀ i, ∑ j ∈ Finset.range T, far i j ≤ 4 / (1 - γ) := fun i =>
    sum_far_le γ hγ0 hγ1 (i + w + 2) T
  rw [variance_fun_sum' (fun j _ => hL2 j)]
  have hcomm : ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T, far j i
      = ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T, far i j := Finset.sum_comm
  calc ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T, cov[U i, U j; E.expLaw T θ]
      ≤ ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T,
          K ^ 2 * (near i j + far i j + far j i) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ = K ^ 2 * (∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T, near i j
          + 2 * ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T, far i j) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        rw [hcomm]
        ring
    _ ≤ K ^ 2 * (∑ _i ∈ Finset.range T, (2 * (w : ℝ) + 3)
          + 2 * ∑ _i ∈ Finset.range T, 4 / (1 - γ)) := by
        have a1 : ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T, near i j
            ≤ ∑ _i ∈ Finset.range T, (2 * (w : ℝ) + 3) :=
          Finset.sum_le_sum fun i _ => hsum_near i
        have a2 : ∑ i ∈ Finset.range T, ∑ j ∈ Finset.range T, far i j
            ≤ ∑ _i ∈ Finset.range T, 4 / (1 - γ) :=
          Finset.sum_le_sum fun i _ => hsum_far i
        exact mul_le_mul_of_nonneg_left (by linarith) hK2
    _ = (T : ℝ) * K ^ 2 * (2 * (w : ℝ) + 3 + 8 / (1 - γ)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        ring
