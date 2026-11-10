-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryEncodedCode_detectable_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:09:34.389264+00:00
-- url     : https://prove2.me/submissions/ca4ea15a-a541-434c-97d9-84280aab9781

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryLocal_compression_detectable
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_compress_inner


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {J : Type} [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_9a39a2a69e_41
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat)
    (S : QuditSubsystem (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2))
    (hS : S.selected.card < f256QuditDistanceBound i) (E : Operator S.selectedSystem) :
    DetectableOn (binaryEncodedCode i).code (S.extendLocalToRegister E) := by
  obtain ⟨c, hc⟩ := binaryLocal_compression_detectable i S hS E
  refine ⟨c, ?_⟩
  rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
  change inner Complex
      (physicalIsometry _ ((f256SourceInput i).encodingIsometry (logicalIsometry _ u)))
      (S.extendLocalToRegister E
        (physicalIsometry _ ((f256SourceInput i).encodingIsometry (logicalIsometry _ v)))) =
    c * inner Complex
      (physicalIsometry _ ((f256SourceInput i).encodingIsometry (logicalIsometry _ u)))
      (physicalIsometry _ ((f256SourceInput i).encodingIsometry (logicalIsometry _ v)))
  rw [(physicalIsometry _).inner_map_map]
  have hh := hc _ ⟨logicalIsometry _ u, rfl⟩ _ ⟨logicalIsometry _ v, rfl⟩
  erw [ComputationalEmbedding.compress_inner] at hh
  exact hh
end QEC.Distillation.Ngu24Binary
