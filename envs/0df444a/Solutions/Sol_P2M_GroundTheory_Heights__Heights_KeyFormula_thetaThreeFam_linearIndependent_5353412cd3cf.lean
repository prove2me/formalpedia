-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThreeFam_linearIndependent_5353412cd3cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:10.445748+00:00
-- url     : https://prove2.me/submissions/2a07af13-c9cc-4b8c-82d4-2017a1727d29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_zeta_three_cube_ebc6a84f8330
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_one_add_zeta_three_add_sq_09cce8161b7e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_third_71b38148d327
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_ne_zero_f16649ac4b2d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution : LinearIndependent ℂ thetaThreeFam := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hE : ∀ w : ℂ, c 0 * thetaThree 0 w + c 1 * thetaThree 1 w + c 2 * thetaThree 2 w = 0 := by
    intro w
    have := congrFun hc (fun _ => w)
    simpa [Fin.sum_univ_three, thetaThreeFam, thetaThreeSec] using this
  have key : ∀ w : ℂ, c 0 * thetaThree 0 w = 0 ∧ c 1 * thetaThree 1 w = 0 ∧
      c 2 * thetaThree 2 w = 0 := by
    intro w
    have e0 := hE w
    have e1 := hE (w + 1 / 3)
    have e2 := hE (w + 1 / 3 + 1 / 3)
    simp only [thetaThree_add_third] at e1 e2
    have hs := one_add_zeta_three_add_sq
    have hc3 := zeta_three_cube
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (1 / 3 : ℂ) * (e0 + e1 + e2) -
        (1 / 3 : ℂ) * (c 1 * thetaThree 1 w + c 2 * thetaThree 2 w) * hs -
        (1 / 3 : ℂ) * c 2 * thetaThree 2 w * zeta3 * hc3
    · linear_combination (1 / 3 : ℂ) * (e0 + zeta3 ^ 2 * e1 + zeta3 * e2) -
        (1 / 3 : ℂ) * (c 0 * thetaThree 0 w + c 2 * thetaThree 2 w) * hs -
        (1 / 3 : ℂ) * (2 * c 1 * thetaThree 1 w + c 2 * thetaThree 2 w * (zeta3 + zeta3 ^ 2)) * hc3
    · linear_combination (1 / 3 : ℂ) * (e0 + zeta3 * e1 + zeta3 ^ 2 * e2) -
        (1 / 3 : ℂ) * (c 0 * thetaThree 0 w + c 1 * thetaThree 1 w) * hs -
        (1 / 3 : ℂ) * (c 1 * thetaThree 1 w * zeta3 + c 2 * thetaThree 2 w * (zeta3 ^ 3 + 2)) * hc3
  intro i
  fin_cases i
  · obtain ⟨w, hw⟩ := thetaThree_ne_zero 0
    exact (mul_eq_zero.mp (key w).1).resolve_right hw
  · obtain ⟨w, hw⟩ := thetaThree_ne_zero 1
    exact (mul_eq_zero.mp (key w).2.1).resolve_right hw
  · obtain ⟨w, hw⟩ := thetaThree_ne_zero 2
    exact (mul_eq_zero.mp (key w).2.2).resolve_right hw
end GroundTheory.Heights₂.Heights.KeyFormula
