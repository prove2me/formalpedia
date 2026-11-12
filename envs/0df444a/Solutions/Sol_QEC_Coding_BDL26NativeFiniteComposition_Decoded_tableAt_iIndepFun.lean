-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.Decoded.tableAt_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:41:55.145008+00:00
-- url     : https://prove2.me/submissions/0327be47-f7af-4039-bff8-79eeabca2350

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_tableAt_preimage
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finite_rectangle_probability
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_tableAt_preimage
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_finite_rectangle_probability
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finite_rectangle_probability
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_tableAt_preimage
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeFiniteComposition
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric BDL26KeyedGeometricExecution BDL26NativeKeyExecutionBridge
open BDL26NativeGeometricExecution BDL26NativeGeometricExecutionCost
open BDL26NativeGeometricScanCost BDL26NativeGeometricJointExecution
open BDL26ReplacementMaterialization BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
open QEC.Coding.BDL26NativeFiniteComposition.Decoded
namespace QEC.Coding.BDL26NativeFiniteComposition.Decoded
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    iIndepFun (tableAt p n) (experimentLaw p n) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hB
  rw [finite_rectangle_probability]
  apply Finset.prod_congr rfl
  intro i hi
  exact (tableAt_preimage p n i (B i) (hB i hi)).symm
end QEC.Coding.BDL26NativeFiniteComposition.Decoded
