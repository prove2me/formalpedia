-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:56.363915+00:00
-- url     : https://prove2.me/submissions/492594fc-d39a-4241-8501-e998e085474d

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
import Theorems.Thm_PositivityTheory_ThKEnd_Two_closedEmb

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
theorem _root_.solution [T2Space R] {C : Fin 2 → Fin 2 → Set R} (h : ∀ i j, IsCompact (C i j)) :
    IsCompact {g : SL(2, R) | ∀ i j, g.1 i j ∈ C i j} :=
  closedEmb.isCompact_preimage (isCompact_pi_infinite fun i => isCompact_pi_infinite (h i))
end PositivityTheory.ThKEnd.Two
