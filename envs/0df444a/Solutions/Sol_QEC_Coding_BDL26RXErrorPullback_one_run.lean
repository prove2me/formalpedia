-- Prove2me | solution 1 for QEC.Coding.BDL26RXErrorPullback.one_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:22:06.909883+00:00
-- url     : https://prove2.me/submissions/b82fbfc1-a263-4e58-831f-721c1210f307

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_one_updated_delta
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_pullback_of_compatible

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXErrorPullback
theorem _root_.solution (_above : 2 ≤ i.val) (h : i.val % 2 = 0) (a : Upper S depth i) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        a + (run S depth i h a).correction + (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l = (run S depth i h a).coarse.val ∧
      ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val =
        (indexedFamily S depth).coboundary1 i.succ (a + (run S depth i h a).correction) ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 :=
  pullback_of_compatible S depth i h (a + (run S depth i h a).correction)
    (run S depth i h a).coarse (one_updated_delta S depth i h a)
end QEC.Coding.BDL26RXErrorPullback
