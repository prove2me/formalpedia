-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.STD.herm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:47:19.12748+00:00
-- url     : https://prove2.me/submissions/2308e7d4-1b2c-457a-a916-67a2c3671847

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.STD
theorem _root_.solution : herm (0 : Vr n) = 0 := by
  ext i j; simp [herm]
end PositivityTheory.Rg.Sw.LVs.STD
