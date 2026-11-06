-- Prove2me | solution 1 for QEC.Locality.card_word_eq_card_bitstring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:44.03117+00:00
-- url     : https://prove2.me/submissions/ad5c3661-7c6b-41d8-a9f8-22507696e041

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι) :
    Fintype.card (Coding.Word (ZMod 2) S.SelectedCoordinates) =
      Fintype.card (Qubit.Bitstring S.SelectedCoordinates) := by
  exact Fintype.card_congr (PauliSymplectic.bitstringWordEquiv _).symm
end QEC.Locality
