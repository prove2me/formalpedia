-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.lowerRepresentative_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:56:03.762073+00:00
-- url     : https://prove2.me/submissions/7bbb77ea-45bd-4e4d-90df-c50d080e032d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (S : OddScale) (d : Nat) (i : StepIndex d) (hi : 2 ≤ i.val)
    (e : (indexedFamily S d).Cochain1 i.succ) :
    ((indexedDecoderData S d).selectedMap i).map1 (lowerRepresentative S d i hi e) =
      e + (actualStep S d i (errorInput S d i e)).correction +
        (indexedFamily S d).coboundary0 i.succ (fullPotential S d i hi e) ∧
    (indexedFamily S d).coboundary1 i.castSucc (lowerRepresentative S d i hi e) =
      (actualStep S d i (errorInput S d i e)).coarse.val ∧
    (indexedFamily S d).coboundary1 i.succ
      ((indexedFamily S d).coboundary0 i.succ (fullPotential S d i hi e)) = 0 :=
  Classical.choose_spec (Classical.choose_spec (actual_pullback S d i hi e))
end QEC.Coding.BDL26HistorySyndromeSensitivity
