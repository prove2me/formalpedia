-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneIntegral_space_one_1f6611ae8ff0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:04.706516+00:00
-- url     : https://prove2.me/submissions/7b64c23a-7db9-4bd4-a11c-4875af9efb37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPlaneSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeToProjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce


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
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (e : ℕ) :
    coneIntegral (HermNorm.std (e + 1)) (⊥ : Ideal (MvPolynomial (Fin (e + 1)) ℂ)) e
      (fun _ => 1) = 1 := by
  have hS : {y : EuclideanSpace ℂ (Fin (e + 1)) | ‖y‖ < 1 ∧
        ∀ q ∈ (⊥ : Ideal (MvPolynomial (Fin (e + 1)) ℂ)),
          eval ((HermNorm.std (e + 1)).pointOf y) q = 0} =
      {y : EuclideanSpace ℂ (Fin (e + 1)) | ‖y‖ < 1 ∧ ∀ j : Fin (e + 1), e + 1 ≤ (j : ℕ) → y j = 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Ideal.mem_bot]
    refine and_congr_right fun _ => ⟨fun _ j hj => absurd j.isLt (by omega), fun _ q hq => ?_⟩
    rw [hq, map_zero]
  obtain ⟨h0, htop⟩ := coordBall_mass (n := e + 1) (m := e + 1) le_rfl
  rw [coneIntegral, hS, setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  exact div_self (ENNReal.toReal_ne_zero.mpr ⟨h0.ne', htop.ne⟩)
end GroundTheory.Heights₂.Heights
