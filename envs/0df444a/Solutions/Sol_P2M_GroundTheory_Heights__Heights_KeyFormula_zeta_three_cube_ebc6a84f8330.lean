-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_zeta_three_cube_ebc6a84f8330
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:44.306026+00:00
-- url     : https://prove2.me/submissions/6f6e13ff-91d5-4bfe-9491-2b4b6347dfb1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent

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
theorem _root_.solution : zeta3 ^ 3 = 1 := by
  unfold zeta3
  rw [← Complex.exp_nat_mul, show ((3 : ℕ) : ℂ) * (2 * π * I / 3) = 2 * π * I by push_cast; ring,
    Complex.exp_two_pi_mul_I]
end GroundTheory.Heights₂.Heights.KeyFormula
