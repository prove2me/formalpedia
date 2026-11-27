-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_gaussNormBasic_hyps_7712b68f0459
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:10.742196+00:00
-- url     : https://prove2.me/submissions/3635defc-d25b-4422-9ea8-4c74d56361b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    (∀ i j, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[2]) i j‖ ≤ 1) ∧ (∀ i, ‖(0 : Fin 2 → ℚ_[2]) i‖ ≤ 1) ∧
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℚ_[2]).det ∧
    (∀ i j, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[2])⁻¹ i j‖ ≤ 1) ∧
    (∀ y : Fin 2 → ℚ_[2], (∀ i, ‖y i‖ ≤ 1) → ∃ x : Fin 2 → ℚ_[2], (∀ k, ‖x k‖ ≤ 1) ∧
      (1 : Matrix (Fin 2) (Fin 2) ℚ_[2]).mulVec x = y) := by
  have h1 : ∀ i j, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[2]) i j‖ ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨h1, fun i ↦ by simp, by simp, by simp [h1], fun y hy ↦ ⟨y, hy, by simp⟩⟩
end GroundTheory.Heights₂.Heights
