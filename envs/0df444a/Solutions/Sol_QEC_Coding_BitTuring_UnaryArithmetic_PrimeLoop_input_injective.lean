-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:48.502123+00:00
-- url     : https://prove2.me/submissions/b0d0a481-c6dc-4332-a8af-90f46641d6ca

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrimality
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_tripleInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
theorem _root_.solution : Function.Injective input := by
  intro x y h
  have he := FactorTest.tripleInput_injective (a₁ := (2,(2,x.val))) (a₂ := (2,(2,y.val))) h
  exact Subtype.ext (congrArg (fun t : ℕ×(ℕ×ℕ) => t.2.2) he)
end QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
