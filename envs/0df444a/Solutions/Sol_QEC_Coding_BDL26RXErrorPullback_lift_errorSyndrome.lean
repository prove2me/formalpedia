-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.lift_errorSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:58:58.392219+00:00
-- url     : https://prove2.me/submissions/928a8254-0f37-4980-b399-b0b5d621d5db

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXErrorPullback
theorem _root_.solution (h : i.val % 2 = 0) (a : Lower S depth i) :
    errorSyndrome S depth i (liftError S depth i a) =
      embeddedSyndrome S depth i h
        ⟨(indexedFamily S depth).coboundary1 i.castSucc a, ⟨a,rfl⟩⟩ := by
  apply Subtype.ext
  exact LinearMap.congr_fun (((indexedDecoderData S depth).rxMap i).commutes_coboundary1) a
end QEC.Coding.BDL26RXErrorPullback
