-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.mX_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:14.721523+00:00
-- url     : https://prove2.me/submissions/fcb12827-98f8-4a35-a519-0cc14b1ac0c0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_Cm_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Cm_mul_CmI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : mX (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 1 = 1 := by
  rw [mX, Matrix.fromBlocks_one, Matrix.mul_one, dp_Cm_inv, Cm_mul_CmI]
end PositivityTheory.Rg.Sw.LVs
