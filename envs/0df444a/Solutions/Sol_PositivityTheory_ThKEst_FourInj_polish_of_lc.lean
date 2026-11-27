-- Prove2me | solution 1 for PositivityTheory.ThKEst.FourInj.polish_of_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:11.781098+00:00
-- url     : https://prove2.me/submissions/35e18f60-f9c0-4a4d-b4d3-6e9f147eb497

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_FourierInjA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory BoundedContinuousFunction
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.FourInj
namespace PositivityTheory.ThKEst.FourInj
theorem _root_.solution (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] : PolishSpace G := by
  let _ : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  have : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : TopologicalSpace.IsCompletelyMetrizableSpace G := inferInstance
  infer_instance
end PositivityTheory.ThKEst.FourInj
