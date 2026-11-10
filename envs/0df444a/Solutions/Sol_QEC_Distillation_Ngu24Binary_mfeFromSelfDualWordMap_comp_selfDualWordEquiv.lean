-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.mfeFromSelfDualWordMap_comp_selfDualWordEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:33:58.099922+00:00
-- url     : https://prove2.me/submissions/98774e73-925f-4f07-8178-bc8d050c8fa2

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Theorems.Thm_QEC_Coding_f256MFEFromSelfDual_apply_basis_coordinates


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable (J : Type)
set_option maxRecDepth 2048
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution :
    (mfeFromSelfDualWordMap J).comp (selfDualWordEquiv J).toLinearMap =
      physicalWordEmbedding J := by
  apply LinearMap.ext
  intro u
  funext x
  change f256MFEFromSelfDual (f256SelfDualBasis.equivFun (u x.1)) x.2 =
    f256MFESigma (u x.1) x.2
  exact congrFun (f256MFEFromSelfDual_apply_basis_coordinates (u x.1)) x.2
end QEC.Distillation.Ngu24Binary
