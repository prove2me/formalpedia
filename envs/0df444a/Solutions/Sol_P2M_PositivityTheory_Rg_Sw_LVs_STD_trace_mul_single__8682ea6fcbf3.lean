-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_STD_trace_mul_single__8682ea6fcbf3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:00.107816+00:00
-- url     : https://prove2.me/submissions/e6b9e500-ae89-497e-8bc9-d326c85d35e7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution (β : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n) :
    (β * Matrix.single r c 1).trace = β c r := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]
end PositivityTheory.Rg.Sw.LVs.STD
