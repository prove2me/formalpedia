-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryEncodedCode_code_eq_cssCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:41:49.74021+00:00
-- url     : https://prove2.me/submissions/4bbf4f21-dc41-4aa2-acc8-682f7bdd7524

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_carrier_eq_cssCarrier

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    (binaryEncodedCode i).code = (binaryCSSCode i).stabilizer.code := by
  cases hE : (binaryEncodedCode i).code with
  | mk E =>
    cases hC : (binaryCSSCode i).stabilizer.code with
    | mk C =>
      have h := binaryEncodedCode_carrier_eq_cssCarrier i
      rw [hE, hC] at h
      exact congrArg QuantumCode.mk h
end QEC.Distillation.Ngu24Binary
