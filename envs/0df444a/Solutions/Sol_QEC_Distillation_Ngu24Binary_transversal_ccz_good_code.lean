-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.transversal_ccz_good_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:00:56.564198+00:00
-- url     : https://prove2.me/submissions/97a3da6e-979d-403e-9416-474b99b8d4f6

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryFamily
import Definitions.Def_QEC_Results_Distillation_TransversalCCZFamily
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCSSCode_dimension
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCSSCode_distance
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_bounds
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_source_lower
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_code_eq_cssCode
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodingIsometry_selfDual_apply
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryFamily_factorCount
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryFamily_selected_density
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryFamily_tensor_intertwining
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryLength_eq_card
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryLength_tendsto_atTop
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryLogicalCount_bounds
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTripleSupport_card
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTripleSupport_disjoint


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution :
    Tendsto binaryLength atTop atTop ∧
    ∀ i : Nat,
      binaryLength i = 512 * (f256GarciaStichtenothLength i - f256MultiplicationLogicalCount i) ∧
      binaryLength i = Fintype.card ((f256SourceInput i).PivotComplement × Fin 512) ∧
      f256MultiplicationLogicalCount i = f256GarciaStichtenothLength i / 10 ∧
      (binaryEncodedCode i).code = (binaryCSSCode i).stabilizer.code ∧
      (binaryCSSCode i).stabilizer.code.dimension = 2 ^ f256MultiplicationLogicalCount i ∧
      QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i) ∧
      (¬ QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i + 1)) ∧
      (f256GarciaStichtenothLength i : ℚ) / 5 - f256MultiplicationLogicalCount i ≤ binaryDistance i ∧
      ((binaryLength i : ℚ) / 10240 ≤ f256MultiplicationLogicalCount i ∧
        (f256MultiplicationLogicalCount i : ℚ) ≤ binaryLength i) ∧
      ((binaryLength i : ℚ) / 5120 ≤ binaryDistance i ∧ (binaryDistance i : ℚ) ≤ binaryLength i) ∧
      (binaryLength i : ℚ) / 512 ≤ (binarySelectedSites (f256SourceInput i).PivotComplement).card ∧
      (∀ x, (binaryTripleSupport (f256SourceInput i).PivotComplement x).card = 3) ∧
      (∀ x y, x ≠ y → Disjoint
        (binaryTripleSupport (f256SourceInput i).PivotComplement x)
        (binaryTripleSupport (f256SourceInput i).PivotComplement y)) ∧
      (binaryPhysicalFactorization (J := (f256SourceInput i).PivotComplement)).factorCount =
        (binarySelectedSites (f256SourceInput i).PivotComplement).card ∧
      (∀ phi : Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i)),
        binaryEncodingIsometry i phi =
          mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement
            (selfDualIsometry (f256SourceInput i).PivotComplement
              ((f256SourceInput i).encodingLinearMap
                (logicalIsometry (Fin (f256MultiplicationLogicalCount i)) phi)))) ∧
      ∀ psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i)),
        binaryPhysicalCCZ
            (taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
              ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi) =
          taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
            ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap
              (binaryLogicalCCZ psi) := by
  refine ⟨binaryLength_tendsto_atTop, fun i => ?_⟩
  exact ⟨rfl, binaryLength_eq_card i, rfl, binaryEncodedCode_code_eq_cssCode i, binaryCSSCode_dimension i,
    (binaryCSSCode_distance i).1, (binaryCSSCode_distance i).2,
    binaryDistance_source_lower i, binaryLogicalCount_bounds i, binaryDistance_bounds i,
    binaryFamily_selected_density i, binaryTripleSupport_card _,
    fun _ _ h => binaryTripleSupport_disjoint _ h, binaryFamily_factorCount i,
    binaryEncodingIsometry_selfDual_apply i,
    binaryFamily_tensor_intertwining i⟩
end QEC.Distillation.Ngu24Binary
