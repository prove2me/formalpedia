-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.tableAt_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:56:58.495037+00:00
-- url     : https://prove2.me/submissions/f05701e3-f834-4bc2-a959-c6a09e14db75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurePreserving_tableAt
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurePreserving_tableAt


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
namespace QEC.Coding.BDL26NativeFiniteComposition
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (experimentLaw p n).map (tableAt p n i) = freshLaw p i.val :=
  (measurePreserving_tableAt p n i).map_eq
end QEC.Coding.BDL26NativeFiniteComposition
