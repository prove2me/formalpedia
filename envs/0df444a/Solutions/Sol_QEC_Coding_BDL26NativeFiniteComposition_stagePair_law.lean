-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.stagePair_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:53:09.628567+00:00
-- url     : https://prove2.me/submissions/75bf0ae7-745a-44de-893c-5beb77afa3f3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_prefix
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurePreserving_prefix
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_freshPair
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_freshPair_law
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stagePair_eq_freshPair_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_freshPair_law
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_freshPair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurePreserving_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePair_eq_freshPair_prefix


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
    (experimentLaw p n).map (stagePair p n i) =
      (outputLaw p i.val).prod (freshLaw p i.val) := by
  rw [stagePair_eq_freshPair_prefix, ← Measure.map_map
    (measurable_freshPair p i.val) (measurable_prefix p i.isLt),
    (measurePreserving_prefix p i.isLt).map_eq, freshPair_law]
end QEC.Coding.BDL26NativeFiniteComposition
