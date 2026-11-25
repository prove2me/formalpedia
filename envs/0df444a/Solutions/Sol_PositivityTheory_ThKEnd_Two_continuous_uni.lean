-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.continuous_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:22.259684+00:00
-- url     : https://prove2.me/submissions/08b49f6e-3d2b-4a04-8b98-647e3c2ffdb3

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
theorem _root_.solution : Continuous (uni : Multiplicative R → SL(2, R)) :=
  Continuous.subtype_mk (continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_toAdd]) _
end PositivityTheory.ThKEnd.Two
