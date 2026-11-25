-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.closedEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:05.693971+00:00
-- url     : https://prove2.me/submissions/0bd9734f-bed5-446b-831b-85518bef1e54

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
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution [T2Space R] : IsClosedEmbedding (Subtype.val : SL(2, R) → Matrix (Fin 2) (Fin 2) R) :=
  (isClosed_eq (continuous_id.matrix_det) continuous_const).isClosedEmbedding_subtypeVal
end PositivityTheory.ThKEnd.Two
