-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.taggedPhysicalIsometry_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:50:00.727812+00:00
-- url     : https://prove2.me/submissions/9a870a7a-6263-4ba3-b96b-4e5b27937902

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_isometry_basis


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
variable [Fintype J] [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (u : TaggedThreeCopyRegisterLabel F256 J) :
    taggedPhysicalIsometry J (registerBasisKet u) =
      registerBasisKet (taggedPhysicalWordEmbedding J u) :=
  ComputationalEmbedding.isometry_basis _ _
end QEC.Distillation.Ngu24Binary
