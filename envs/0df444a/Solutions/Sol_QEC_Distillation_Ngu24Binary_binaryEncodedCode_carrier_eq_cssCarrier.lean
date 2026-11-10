-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryEncodedCode_carrier_eq_cssCarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:30:47.935571+00:00
-- url     : https://prove2.me/submissions/b6f15381-ca1c-4cde-87f2-88d1056961f0

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCSSCode_dimension
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_carrier_le_cssCarrier
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_dimension


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    (binaryEncodedCode i).code.carrier = (binaryCSSCode i).stabilizer.code.carrier := by
  apply Submodule.eq_of_le_of_finrank_eq (binaryEncodedCode_carrier_le_cssCarrier i)
  exact (binaryEncodedCode_dimension i).trans (binaryCSSCode_dimension i).symm
end QEC.Distillation.Ngu24Binary
