-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:59.083201+00:00
-- url     : https://prove2.me/submissions/1339706a-76d5-4264-a323-256562498628

import Definitions.Def_QEC_Coding_BitTuring_UnaryProductTrial
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Definitions.Def_QEC_Coding_BitTuring_UnaryProductSearch
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularTrial_productInput_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch
open Turing StateTransition
open SquareRoot (readNat afterNat readNat_prefix afterNat_prefix readNat_unary state_succ_after)
namespace QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch
theorem _root_.solution : Function.Injective input := by
  intro x y h
  have he := ModularTrial.productInput_injective (a₁:=((0,(x.val.2.1,⟨x.val.2.2,x.property.1⟩)),x.val.1))
    (a₂:=((0,(y.val.2.1,⟨y.val.2.2,y.property.1⟩)),y.val.1)) h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.2) he)
    (Prod.ext (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.1.2.1) he)
      (congrArg (fun z:(ℕ×(ℕ×ℕ+))×ℕ => z.1.2.2.val) he))
end QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch
