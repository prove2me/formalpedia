-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:17:23.380071+00:00
-- url     : https://prove2.me/submissions/55b9e6d2-8aa1-45bc-88fc-7634f7cf7686

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularTrial_productInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot
theorem _root_.solution : Function.Injective input := by
  intro x y h
  have he := ModularTrial.productInput_injective (a₁:=((0,(0,⟨x.val.2,x.property.1⟩)),x.val.1))
    (a₂:=((0,(0,⟨y.val.2,y.property.1⟩)),y.val.1)) h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.2) he)
    (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.1.2.2.val) he)
end QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot
