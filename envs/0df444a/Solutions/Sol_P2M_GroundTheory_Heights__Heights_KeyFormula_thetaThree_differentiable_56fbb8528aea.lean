-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_differentiable_56fbb8528aea
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:06.146914+00:00
-- url     : https://prove2.me/submissions/5154421b-2e49-4041-8e17-0ace21b9c283

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_im_three_I_pos_32484545ae83

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
theorem _root_.solution (ν : ℕ) : Differentiable ℂ (thetaThree ν) := by
  intro w
  have h1 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w (3 * I)) (3 * w + ν * I) :=
    differentiableAt_jacobiTheta₂_fst _ im_three_I_pos
  have h2 : DifferentiableAt ℂ (fun w : ℂ => 3 * w + ν * I) w := by fun_prop
  have h3 : DifferentiableAt ℂ ((fun w : ℂ => jacobiTheta₂ w (3 * I)) ∘ (fun w : ℂ => 3 * w + ν * I)) w :=
    DifferentiableAt.comp w h1 h2
  exact (by fun_prop : DifferentiableAt ℂ
    (fun w : ℂ => cexp (π * I * ν ^ 2 * I / 3 + 2 * π * I * ν * w)) w).mul h3
end GroundTheory.Heights₂.Heights.KeyFormula
