-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FactorTest.tripleInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:14:44.717059+00:00
-- url     : https://prove2.me/submissions/a72ab59b-3459-4a01-bf2a-d8a7b63e6d71

import Definitions.Def_QEC_Coding_BitTuring_UnaryComparison
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_tripleInput_takeWhile
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_tripleInput_dropWhile
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_pairInput_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
theorem _root_.solution :
    Function.Injective (fun x : ℕ × (ℕ × ℕ) => tripleInput x.1 x.2.1 x.2.2) := by
  intro x y h
  have ha := congrArg (List.takeWhile id) h
  rw [tripleInput_takeWhile,tripleInput_takeWhile] at ha
  have hrest := congrArg (List.dropWhile id) h
  rw [tripleInput_dropWhile,tripleInput_dropWhile] at hrest
  exact Prod.ext (unary_injective ha) (pairInput_injective (List.cons.inj hrest).2)
end QEC.Coding.BitTuring.UnaryArithmetic.FactorTest
