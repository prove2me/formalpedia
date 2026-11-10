-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryEncodingIsometry_selfDual_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:50:15.640066+00:00
-- url     : https://prove2.me/submissions/021944d3-c8dd-447e-9fcd-37c080a7280e

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodingIsometry_selfDual_factorization

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary.binarySelfDualFieldWordFintype
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat)
    (psi : Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i))) :
    binaryEncodingIsometry i psi =
      mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement
        (selfDualIsometry (f256SourceInput i).PivotComplement
          ((f256SourceInput i).encodingLinearMap
            (logicalIsometry (Fin (f256MultiplicationLogicalCount i)) psi))) :=
  LinearMap.congr_fun (binaryEncodingIsometry_selfDual_factorization i) psi
end QEC.Distillation.Ngu24Binary
