-- Prove2me | solution 1 for RobustRegLasso.FeatureWise.eq_5_worst_case_attained
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:21:53.97427+00:00
-- url     : https://prove2.me/submissions/07105b75-c53e-4c69-b724-d00e2faca58e

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic

open RobustRegLasso.FeatureWise

private lemma scalar_sign_identity (r : ℝ) : r * Real.sign r = |r| := by
  obtain hn | rfl | hp := lt_trichotomy r 0
  · simp [Real.sign_of_neg hn, abs_of_neg hn]
  · simp
  · simp [Real.sign_of_pos hp, abs_of_pos hp]

theorem solution {n m : ℕ} (hn : 0 < n) (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (x : Fin m → ℝ)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (hu_dir : matVec a x ≠ b → u = ‖b - matVec a x‖⁻¹ • (b - matVec a x)) :
    worstCaseDisturbance c x u ∈ uncertaintySet c ∧
      perturbedResidual a (worstCaseDisturbance c x u) b x =
        ‖b - matVec a x‖ + ∑ i, c i * |x i| := by
  have hfeasible : worstCaseDisturbance c x u ∈ uncertaintySet c := by
    intro i
    simp only [worstCaseDisturbance, norm_smul, Real.norm_eq_abs, abs_neg, abs_mul,
      abs_of_nonneg (hc i), hu, mul_one]
    obtain hs | hs | hs := Real.sign_apply_eq (x i)
    · simp [hs]
    · simpa [hs] using hc i
    · simp [hs]
  have hdist : matVec (worstCaseDisturbance c x u) x =
      (-(∑ i, c i * |x i|)) • u := by
    unfold matVec worstCaseDisturbance
    simp_rw [smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      x i * -(c i * Real.sign (x i)) = -(c i * (x i * Real.sign (x i))) := by ring
      _ = -(c i * |x i|) := by rw [scalar_sign_identity]
  have hresidual : b - matVec a x = ‖b - matVec a x‖ • u := by
    by_cases heq : matVec a x = b
    · simp [heq]
    · have hne : b - matVec a x ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
      rw [hu_dir heq, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_smul]
  have hmat : matVec (a + worstCaseDisturbance c x u) x =
      matVec a x + matVec (worstCaseDisturbance c x u) x := by
    simp [matVec, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  refine ⟨hfeasible, ?_⟩
  unfold perturbedResidual
  rw [hmat, sub_add_eq_sub_sub, hdist]
  conv_lhs => rw [hresidual, ← sub_smul, sub_neg_eq_add]
  rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
  exact abs_of_nonneg (add_nonneg (norm_nonneg (b - matVec a x)) (Finset.sum_nonneg fun i hi =>
    mul_nonneg (hc i) (abs_nonneg _)))

#print axioms solution
