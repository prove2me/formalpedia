-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.contIpB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:40.430951+00:00
-- url     : https://prove2.me/submissions/160853b3-69b1-4b38-962e-637158c01055

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_CardAddB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution {n : ℕ} (y : E n) : Continuous fun β : E n => ip β y := by
  unfold ip
  fun_prop
end PositivityTheory.Rg.Sw.WR.D
