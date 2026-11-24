-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.uni_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:16.808857+00:00
-- url     : https://prove2.me/submissions/f7923fd4-cec8-4378-935d-5d32bb47aed3

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
variable {R : Type} [CommRing R]
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution (x : Multiplicative R) : (uni x).1 = !![1, x.toAdd; 0, 1] := rfl
end PositivityTheory.ThKEnd.Two
