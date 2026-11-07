-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryOutputEquality.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:57.627285+00:00
-- url     : https://prove2.me/submissions/0134625d-7bb7-4c84-97eb-3cf558b00da0

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryOutputEquality
open Turing StateTransition UnaryArithmetic
variable (A : Machine)
namespace QEC.Coding.BitTuring.UnaryOutputEquality
theorem _root_.solution {α : Type} (encode : α→List Bool) (hi : Function.Injective encode) :
    Function.Injective (input encode) := by
  intro x y h
  have he := @prefixInput_injective (x.2,encode x.1) (y.2,encode y.1) h
  exact Prod.ext (hi (congrArg (fun z:ℕ×List Bool => z.2) he))
    (congrArg (fun z:ℕ×List Bool => z.1) he)
end QEC.Coding.BitTuring.UnaryOutputEquality
