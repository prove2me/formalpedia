-- Prove2me | solution 1 for StabilityDichotomies.Solvability.thinning_output_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:38:10.43534+00:00
-- url     : https://prove2.me/submissions/eeb27b1e-5dce-4133-aedf-05797d310f99

import Theorems.Thm_StabilityDichotomies_Solvability_horn_thinning_sensitivity
import Theorems.Thm_StabilityDichotomies_Solvability_dualHorn_thinning_sensitivity
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem solution (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ A : Solver Γ, ThinningOutputLaw Γ b ε A →
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          averageSensitivity A I ≤ C * ε⁻¹ := by
  refine ⟨(maxArity Γ : ℝ) + 1, by positivity, ?_⟩
  intro ε hε hε1 A hLaw V _ I hSat
  have hh : averageSensitivity A I ≤ (maxArity Γ : ℝ) * ε⁻¹ := by
    cases b with
    | false => exact horn_thinning_sensitivity Γ (by simpa using hΓ) ε hε hε1 A hLaw V I hSat
    | true => exact dualHorn_thinning_sensitivity Γ (by simpa using hΓ) ε hε hε1 A hLaw V I hSat
  calc
    _ ≤ (maxArity Γ : ℝ) * ε⁻¹ := hh
    _ ≤ ((maxArity Γ : ℝ) + 1) * ε⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (le_of_lt hε))
      linarith
