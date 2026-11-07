-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.squareInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:15:31.206072+00:00
-- url     : https://prove2.me/submissions/e802c9e4-b052-4821-8883-2c286d732fd4

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_tripleInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
theorem _root_.solution : Function.Injective squareInput := by
  intro x y h
  have he := @FactorTest.tripleInput_injective (x.1,(x.1,x.2.val)) (y.1,(y.1,y.2.val)) h
  exact Prod.ext (congrArg (fun z:ℕ×(ℕ×ℕ) => z.1) he)
    (Subtype.ext (congrArg (fun z:ℕ×(ℕ×ℕ) => z.2.2) he))
end QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
