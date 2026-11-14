-- Prove2me | solution 1 for StabilityDichotomies.Solvability.integrated_occurrence_violation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:50:56.626605+00:00
-- url     : https://prove2.me/submissions/f5746f5c-be68-4dcb-878d-eda376ffaae6

import Theorems.Thm_StabilityDichotomies_Solvability_thinning_absent_marginal
import Theorems.Thm_StabilityDichotomies_Solvability_occurrence_violation_le_omission
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem solution (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (i : Fin I.constraints.card) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε⁻¹ * ∫ p in (1 - ε)..1,
      ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
      (if (occurrenceAt I i).Satisfied (extremalSolution (thinnedInstance I mask) b) then 0 else 1) ≤ ε / 2 := by
  have hcont (mask : Fin I.constraints.card → Bool) : Continuous (fun p : ℝ => retentionWeight p mask) := by
    unfold retentionWeight
    apply continuous_finset_prod
    intro j hj
    cases hm : mask j <;> simp only [hm, Bool.false_eq_true, ↓reduceIte]
    · exact continuous_const.sub continuous_id
    · exact continuous_id
  have hleft : Continuous (fun p : ℝ => ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
      (if (occurrenceAt I i).Satisfied (extremalSolution (thinnedInstance I mask) b) then 0 else 1)) := by
    fun_prop
  have hright : Continuous (fun p : ℝ => ∑ mask : Fin I.constraints.card → Bool,
      retentionWeight p mask * (if mask i then 0 else 1)) := by
    fun_prop
  have hint := intervalIntegral.integral_mono_on (μ := volume) (show 1 - ε ≤ 1 by linarith)
    (hleft.intervalIntegrable _ _) (hright.intervalIntegrable _ _) (by
      intro p hp
      exact occurrence_violation_le_omission Γ b hΓ V I hSat i p (by linarith [hp.1]) (by linarith [hp.2]))
  have h := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (le_of_lt hε))
  rw [thinning_absent_marginal I.constraints.card i ε hε hε1] at h
  exact h

