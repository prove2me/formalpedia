-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryEncodedCode_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:54:57.985422+00:00
-- url     : https://prove2.me/submissions/56147efc-8957-4764-9a47-2e8b0a625154

import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Theorems.Thm_QEC_Distillation_Ngu24Binary_logicalIsometry_basis
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_encodingLinearMap_apply_logical_basis
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_encodingLinearMap_apply_logical_basis


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_3142684436_53
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) (u : Fin (f256MultiplicationLogicalCount i) → ZMod 2) :
    (binaryEncodedCode i).encode (EuclideanSpace.basisFun _ Complex u) =
      physicalIsometry (f256SourceInput i).PivotComplement
        ((f256SourceInput i).shortenedCosetKet
          (logicalWordEmbedding (Fin (f256MultiplicationLogicalCount i)) u)) := by
  change physicalIsometry _ ((f256SourceInput i).encodingLinearMap
    (logicalIsometry _ (EuclideanSpace.basisFun
      (Fin (f256MultiplicationLogicalCount i) → ZMod 2) Complex u))) = _
  rw [logicalIsometry_basis]
  exact congrArg (physicalIsometry _) ((f256SourceInput i).encodingLinearMap_apply_logical_basis _)
end QEC.Distillation.Ngu24Binary
