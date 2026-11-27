-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNormBasic_hyps_7712b68f0459
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:25:46.117262+00:00
-- url     : https://prove2.me/submissions/e412d6d2-02cb-4a86-beb8-b08d88fe44ed

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Mathlib
import Mathlib.Tactic





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
theorem _root_.solution :
    (∀ i j, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[2]) i j‖ ≤ 1) ∧ (∀ i, ‖(0 : Fin 2 → ℚ_[2]) i‖ ≤ 1) ∧
    IsUnit (1 : Matrix (Fin 2) (Fin 2) ℚ_[2]).det ∧
    (∀ i j, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[2])⁻¹ i j‖ ≤ 1) ∧
    (∀ y : Fin 2 → ℚ_[2], (∀ i, ‖y i‖ ≤ 1) → ∃ x : Fin 2 → ℚ_[2], (∀ k, ‖x k‖ ≤ 1) ∧
      (1 : Matrix (Fin 2) (Fin 2) ℚ_[2]).mulVec x = y) := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp []; done)
    | (intros; grind)
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_5_3"



end 
