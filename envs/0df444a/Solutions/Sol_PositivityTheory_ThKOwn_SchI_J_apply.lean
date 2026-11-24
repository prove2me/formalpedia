-- Prove2me | solution 1 for PositivityTheory.ThKOwn.SchI.J_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:33.301147+00:00
-- url     : https://prove2.me/submissions/fbe8595e-d500-425c-b925-c8a5d761a9aa

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_JetApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open PositivityTheory.ThKOwn.SchI
open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKOwn.SchI
theorem _root_.solution (k j : ℕ) (f : SchwartzMap V ℂ) : J k j f = jet k j f := rfl
end PositivityTheory.ThKOwn.SchI
