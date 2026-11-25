-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.ts_continuous_nU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:14.766855+00:00
-- url     : https://prove2.me/submissions/4a137823-0eef-46ce-bc03-e7bf53872f4b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TsContinuousNU

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : Continuous (nU : Matrix (Fin n) (Fin n) ℂ → M2 n) := by
  unfold nU
  exact Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const
end PositivityTheory.Rg.Sw.LVs
