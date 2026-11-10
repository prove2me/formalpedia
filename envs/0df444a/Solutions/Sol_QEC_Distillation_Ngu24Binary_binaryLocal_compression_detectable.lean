-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryLocal_compression_detectable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:02:03.708631+00:00
-- url     : https://prove2.me/submissions/95f791b9-6466-47dc-9667-6818a19f4245

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
import Theorems.Thm_QEC_Distillation_Ngu24Binary_physicalWordEmbedding_difference_outside
import Theorems.Thm_QEC_Distillation_Ngu24Binary_physicalWordEmbedding_agrees_on
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_detectableOn_of_coset_locality
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_complement_separates
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_kernel_restrict_surjective
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_compress_basis_inner
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_basis_diagonal_eq
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_basis_inner_zero


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
    DetectableOn (f256SourceInput i).quantumCode
      (ComputationalEmbedding.compress
        ⟨physicalWordEmbedding (f256SourceInput i).PivotComplement,
          physicalWordEmbedding_injective (f256SourceInput i).PivotComplement⟩
        (S.extendLocalToRegister E)) := by
  let B := S.selected.image Prod.fst
  have hB : B.card < f256QuditDistanceBound i :=
    (Finset.card_image_le).trans_lt hS
  apply (f256SourceInput i).detectableOn_of_coset_locality _ B
    (f256SourceInput_complement_separates i B hB)
    (f256SourceInput_kernel_restrict_surjective i B hB)
  · intro x y hxy
    change inner Complex (EuclideanSpace.basisFun _ Complex x)
      (ComputationalEmbedding.compress _ _ (EuclideanSpace.basisFun _ Complex y)) = 0
    erw [ComputationalEmbedding.compress_basis_inner]
    apply QuditSubsystem.extendLocal_basis_inner_zero
    exact physicalWordEmbedding_difference_outside S.selected x y hxy
  · intro x y hxy
    change inner Complex (EuclideanSpace.basisFun _ Complex x)
      (ComputationalEmbedding.compress _ _ (EuclideanSpace.basisFun _ Complex x)) =
      inner Complex (EuclideanSpace.basisFun _ Complex y)
        (ComputationalEmbedding.compress _ _ (EuclideanSpace.basisFun _ Complex y))
    let e : Word F256 (f256SourceInput i).PivotComplement ↪
        Qudit.Label (fun _ : (f256SourceInput i).PivotComplement × Fin 512 => 2) :=
      ⟨physicalWordEmbedding (f256SourceInput i).PivotComplement,
        physicalWordEmbedding_injective (f256SourceInput i).PivotComplement⟩
    exact (ComputationalEmbedding.compress_basis_inner e (S.extendLocalToRegister E) x x).trans
      ((QuditSubsystem.extendLocal_basis_diagonal_eq S E (e x) (e y)
        (physicalWordEmbedding_agrees_on S.selected x y hxy)).trans
        (ComputationalEmbedding.compress_basis_inner e (S.extendLocalToRegister E) y y).symm)
end QEC.Distillation.Ngu24Binary
