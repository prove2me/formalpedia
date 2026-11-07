-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.squareTrialInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:56:49.094067+00:00
-- url     : https://prove2.me/submissions/36dc303f-9cb3-4d46-8dfb-db1c9d79d14a

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularTrial_squareInput_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ModularProduct_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_Remainder_input_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_input_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
theorem _root_.solution :
    Function.Injective (UnaryOutputEquality.input squareInput) :=
  UnaryOutputEquality.input_injective squareInput squareInput_injective
end QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
