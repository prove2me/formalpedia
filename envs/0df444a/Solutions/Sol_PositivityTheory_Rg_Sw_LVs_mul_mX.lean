-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.mul_mX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:40.6113+00:00
-- url     : https://prove2.me/submissions/18a2c6e8-d7f5-4a0a-9d42-e51efae18595

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_WD_split
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_mX_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) : x * mX 1 Q R 1 = x + x * WD Q 0 + x * WD 0 R := by
  rw [mX_eq, Matrix.mul_add, Matrix.mul_one, WD_split, Matrix.mul_add, add_assoc]
end PositivityTheory.Rg.Sw.LVs
