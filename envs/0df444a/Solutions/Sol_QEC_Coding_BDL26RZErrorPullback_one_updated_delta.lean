-- Prove2me | solution 1 for QEC.Coding.BDL26RZErrorPullback.one_updated_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:24:33.67012+00:00
-- url     : https://prove2.me/submissions/0fec975c-db8a-4b19-8a5f-530970becd2e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_correction_delta
section
noncomputable section
namespace QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
private theorem word_add_self {α : Type*} (w : Word (ZMod 2) α) : w + w = 0 := by
  funext q
  exact CharTwo.add_self_eq_zero (w q)
section History
variable (n : Nat) (sigma : BDL26CanonicalHistoryMarks.Input S n) (k : StepIndex n)
end History
end QEC.Coding.BDL26RZErrorPullback
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RZErrorPullback
theorem _root_.solution (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (a + (run S depth i h a).correction) =
      ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by
  rw [map_add, correction_delta]
  change (errorSyndrome S depth i a).val + ((errorSyndrome S depth i a).val + _) = _
  rw [← add_assoc, word_add_self, zero_add]
end QEC.Coding.BDL26RZErrorPullback
