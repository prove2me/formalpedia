-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.two_le_infty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:20.583457+00:00
-- url     : https://prove2.me/submissions/5dd7ce79-d207-4fab-9eea-102f0305805e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Imports
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarDir
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivEqZeroOfVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
end PositivityTheory.Rg.Sw.LVs
