-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.nexpB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:49:42.28326+00:00
-- url     : https://prove2.me/submissions/4a79fd7b-8a76-44ad-b226-3787868cfb22

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
theorem _root_.solution (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by
  rw [Complex.norm_exp]
  simp
end PositivityTheory.Rg.Sw.WR.D
