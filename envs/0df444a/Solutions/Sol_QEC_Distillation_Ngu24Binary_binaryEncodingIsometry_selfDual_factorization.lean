-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryEncodingIsometry_selfDual_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:45:03.568958+00:00
-- url     : https://prove2.me/submissions/d2e6d7e5-7c35-45ae-b300-088855c8491a

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Theorems.Thm_QEC_Distillation_Ngu24Binary_physicalIsometry_eq_selfDual_comp

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary.binarySelfDualFieldWordFintype
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    (binaryEncodingIsometry i).toLinearMap =
      (mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement).toLinearMap.comp
        ((selfDualIsometry (f256SourceInput i).PivotComplement).toLinearMap.comp
          ((f256SourceInput i).encodingLinearMap.comp
            (logicalIsometry (Fin (f256MultiplicationLogicalCount i))).toLinearMap)) := by
  change (physicalIsometry _).toLinearMap.comp _ = _
  rw [physicalIsometry_eq_selfDual_comp, LinearMap.comp_assoc]
  rfl
end QEC.Distillation.Ngu24Binary
