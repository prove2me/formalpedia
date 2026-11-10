-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.physicalIsometry_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:41:11.814007+00:00
-- url     : https://prove2.me/submissions/2ae14a48-0b8a-4007-aea9-57848d025f01

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
theorem _root_.solution (u : J → F256) :
    physicalIsometry J (EuclideanSpace.basisFun (J → F256) Complex u) =
      EuclideanSpace.basisFun ((J × Fin 512) → ZMod 2) Complex (physicalWordEmbedding J u) :=
  ComputationalEmbedding.isometry_basis _ _
end QEC.Distillation.Ngu24Binary
