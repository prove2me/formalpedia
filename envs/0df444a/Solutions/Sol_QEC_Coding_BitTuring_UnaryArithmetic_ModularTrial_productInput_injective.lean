-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.productInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:09.252562+00:00
-- url     : https://prove2.me/submissions/71168d4e-7c60-4f6f-ba81-99c0e97a072c

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
theorem _root_.solution :
    Function.Injective (UnaryOutputEquality.input ModularProduct.input) :=
  UnaryOutputEquality.input_injective ModularProduct.input ModularProduct.input_injective
end QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
