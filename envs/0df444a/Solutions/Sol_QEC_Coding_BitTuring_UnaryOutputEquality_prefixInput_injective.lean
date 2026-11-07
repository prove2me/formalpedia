-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryOutputEquality.prefixInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:08:08.991192+00:00
-- url     : https://prove2.me/submissions/720393b3-eb08-4808-88b2-5cd1bece0aeb

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_takeWhile
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_dropWhile
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryOutputEquality
open Turing StateTransition UnaryArithmetic
variable (A : Machine)
namespace QEC.Coding.BitTuring.UnaryOutputEquality
theorem _root_.solution :
    Function.Injective (fun z:ℕ×List Bool => prefixInput z.1 z.2) := by
  intro x y h
  have hr : unary x.1=unary y.1 := by
    simpa only [prefixInput_takeWhile] using congrArg (List.takeWhile id) h
  have hx : false::x.2=false::y.2 := by
    simpa only [prefixInput_dropWhile] using congrArg (List.dropWhile id) h
  exact Prod.ext (unary_injective hr) (List.cons.inj hx).2
end QEC.Coding.BitTuring.UnaryOutputEquality
