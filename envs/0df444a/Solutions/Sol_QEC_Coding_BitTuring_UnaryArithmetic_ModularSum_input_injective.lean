-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularSum.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:15:25.601813+00:00
-- url     : https://prove2.me/submissions/4f3df579-8a07-46e6-8de4-8eeab4dc9b1b

import Definitions.Def_QEC_Coding_BitTuring_UnaryRemainder
import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTest
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularSum
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FactorTest_tripleInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularSum
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularSum
theorem _root_.solution : Function.Injective input := by
  intro x y h
  have he := @FactorTest.tripleInput_injective (x.1,(x.2.1,x.2.2.val)) (y.1,(y.2.1,y.2.2.val)) h
  have ha : x.1=y.1 := congrArg (fun z:ℕ×(ℕ×ℕ) => z.1) he
  have hb : x.2.1=y.2.1 := congrArg (fun z:ℕ×(ℕ×ℕ) => z.2.1) he
  have hq : x.2.2.val=y.2.2.val := congrArg (fun z:ℕ×(ℕ×ℕ) => z.2.2) he
  exact Prod.ext ha (Prod.ext hb (Subtype.ext hq))
end QEC.Coding.BitTuring.UnaryArithmetic.ModularSum
