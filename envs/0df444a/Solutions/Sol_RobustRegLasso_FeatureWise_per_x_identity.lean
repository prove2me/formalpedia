-- Prove2me | solution 1 for RobustRegLasso.FeatureWise.per_x_identity
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:28:34.654465+00:00
-- url     : https://prove2.me/submissions/34b98324-6509-432f-a9c2-b4c84e51a0fa

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic
import Theorems.Thm_RobustRegLasso_FeatureWise_eq_4_upper_bound
import Theorems.Thm_RobustRegLasso_FeatureWise_eq_5_worst_case_attained

open RobustRegLasso.FeatureWise

theorem solution {n m : ℕ} (hn : 0 < n) (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (x : Fin m → ℝ) :
    IsGreatest (residualValues a b c x) (‖b - matVec a x‖ + ∑ i, c i * |x i|) ∧
      robustObjective a b c x = ((‖b - matVec a x‖ + ∑ i, c i * |x i| : ℝ) : EReal) := by
  have hex : ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
      (matVec a x ≠ b → u = ‖b - matVec a x‖⁻¹ • (b - matVec a x)) := by
    by_cases heq : matVec a x = b
    · refine ⟨PiLp.single 2 (⟨0, hn⟩ : Fin n) (1 : ℝ), ?_, ?_⟩
      · simp
      · intro hne
        exact (hne heq).elim
    · refine ⟨‖b - matVec a x‖⁻¹ • (b - matVec a x), ?_, fun _ => rfl⟩
      have hne : ‖b - matVec a x‖ ≠ 0 := norm_ne_zero_iff.mpr
        (sub_ne_zero.mpr (Ne.symm heq))
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (b - matVec a x))), inv_mul_cancel₀ hne]
  obtain ⟨u, hu, hdir⟩ := hex
  obtain ⟨hfeasible, hattain⟩ := eq_5_worst_case_attained hn a b c hc x u hu hdir
  have hupper (δ : Fin m → EuclideanSpace ℝ (Fin n)) (hδ : δ ∈ uncertaintySet c) :
      perturbedResidual a δ b x ≤ ‖b - matVec a x‖ + ∑ i, c i * |x i| := by
    simpa only [mul_comm] using eq_4_upper_bound a b c hc x δ hδ
  constructor
  · refine ⟨⟨worstCaseDisturbance c x u, hfeasible, hattain⟩, ?_⟩
    rintro y ⟨δ, hδ, rfl⟩
    exact hupper δ hδ
  · unfold robustObjective
    apply le_antisymm
    · exact iSup_le fun δ => iSup_le fun hδ => EReal.coe_le_coe (hupper δ hδ)
    · rw [← hattain]
      exact le_iSup_of_le (worstCaseDisturbance c x u) (le_iSup_of_le hfeasible le_rfl)

#print axioms solution
