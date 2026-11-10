-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.physicalIsometry_eq_selfDual_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:39:02.611677+00:00
-- url     : https://prove2.me/submissions/6cc08aa2-be05-4303-bec1-1032905a215b

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Theorems.Thm_QEC_Distillation_Ngu24Binary_mfeFromSelfDualWordMap_comp_selfDualWordEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_linearMap_comp


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary.binarySelfDualFieldWordFintype
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution :
    (physicalIsometry J).toLinearMap =
      (mfeFromSelfDualIsometry J).toLinearMap.comp (selfDualIsometry J).toLinearMap := by
  have he : (selfDualWordEquiv J).toEquiv.toEmbedding.trans
      ⟨mfeFromSelfDualWordMap J, mfeFromSelfDualWordMap_injective J⟩ =
      ⟨physicalWordEmbedding J, physicalWordEmbedding_injective J⟩ := by
    apply Function.Embedding.ext
    intro u
    exact LinearMap.congr_fun (mfeFromSelfDualWordMap_comp_selfDualWordEquiv J) u
  exact (congrArg ComputationalEmbedding.linearMap he).symm.trans
    (ComputationalEmbedding.linearMap_comp _ _)
end QEC.Distillation.Ngu24Binary
