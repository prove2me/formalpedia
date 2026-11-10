-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.taggedLogicalIsometry_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:52:10.002983+00:00
-- url     : https://prove2.me/submissions/a1f0e457-8a88-49a8-9317-51a115bf41c0

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
theorem _root_.solution (u : TaggedThreeCopyRegisterLabel (ZMod 2) J) :
    taggedLogicalIsometry J (registerBasisKet u) =
      registerBasisKet (logicalWordEmbedding (ThreeCopyTag × J) u) :=
  ComputationalEmbedding.isometry_basis _ _
end QEC.Distillation.Ngu24Binary
