-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_5b4389eedbd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:41.003844+00:00
-- url     : https://prove2.me/submissions/97c01dc7-5206-4b39-8639-5b7dd59450c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_one_17c6616ebd0d

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
theorem _root_.solution (ν : ℕ) (m : ℤ) (w : ℂ) : thetaThree ν (w + m) = thetaThree ν w := by
  induction m using Int.induction_on generalizing w with
  | zero => simp
  | succ j ih => push_cast at ih ⊢; rw [← add_assoc, thetaThree_add_one, ih]
  | pred j ih =>
    push_cast at ih ⊢
    rw [← thetaThree_add_one ν (w + (-(j : ℂ) - 1)),
      show w + (-(j : ℂ) - 1) + 1 = w + -(j : ℂ) by ring, ih]
end GroundTheory.Heights₂.Heights.KeyFormula
