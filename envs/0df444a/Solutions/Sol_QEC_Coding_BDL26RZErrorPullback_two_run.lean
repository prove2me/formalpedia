-- Prove2me | solution 1 for QEC.Coding.BDL26RZErrorPullback.two_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:42:02.44924+00:00
-- url     : https://prove2.me/submissions/6cf5ac75-9e83-42bf-8e74-4f2ce8b3882b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_updated_delta
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_pullback_of_compatible

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RZErrorPullback
theorem _root_.solution (_above : 2 ≤ i.val) (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        a + b + (run S depth i h a).correction + (run S depth i h b).correction +
          (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l =
        (run S depth i h a).coarse.val + (run S depth i h b).coarse.val ∧
      ((indexedDecoderData S depth).selectedMap i).map2
        ((run S depth i h a).coarse.val + (run S depth i h b).coarse.val) =
          (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 :=
  pullback_of_compatible S depth i h (updated S depth i h a b)
    (coarseSum S depth i h a b) (updated_delta S depth i h a b)
end QEC.Coding.BDL26RZErrorPullback
