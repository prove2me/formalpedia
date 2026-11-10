-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.logicalIsometry_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:47:02.405604+00:00
-- url     : https://prove2.me/submissions/2c7ca689-3d64-44e0-af1b-64d4cd25d790

import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_isometry_basis


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
theorem _root_.solution (u : J → ZMod 2) :
    logicalIsometry J (EuclideanSpace.basisFun (J → ZMod 2) Complex u) =
      EuclideanSpace.basisFun (J → F256) Complex (logicalWordEmbedding J u) :=
  ComputationalEmbedding.isometry_basis _ _
end QEC.Distillation.Ngu24Binary
