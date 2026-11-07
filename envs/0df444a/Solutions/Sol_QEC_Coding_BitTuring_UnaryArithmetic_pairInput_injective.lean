-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.pairInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:07:54.377971+00:00
-- url     : https://prove2.me/submissions/377fd00b-a8ef-4a51-abc6-94ee9b1a8872

import Definitions.Def_QEC_Coding_BitTuring_Composition
import Definitions.Def_QEC_Coding_BitTuring_UnaryMultiplication
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_takeWhile_pairInput
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_dropWhile_pairInput

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic
theorem _root_.solution : Function.Injective (fun x : ℕ × ℕ => pairInput x.1 x.2) := by
  intro x y h
  have ha : unary x.1 = unary y.1 := by
    simpa only [takeWhile_pairInput] using congrArg (List.takeWhile id) h
  have hb : false :: unary x.2 = false :: unary y.2 := by
    simpa only [dropWhile_pairInput] using congrArg (List.dropWhile id) h
  exact Prod.ext (unary_injective ha) (unary_injective (List.cons.inj hb).2)
end QEC.Coding.BitTuring.UnaryArithmetic
