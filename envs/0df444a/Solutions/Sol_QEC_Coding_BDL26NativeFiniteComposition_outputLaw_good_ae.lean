-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.outputLaw_good_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:13:57.70976+00:00
-- url     : https://prove2.me/submissions/8cc10f80-ba7b-4a6c-8eb3-2408718c628f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_outputLaw_succ
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_succ
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_random_input_geometry_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_boundedDensityLocalMap
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_replacementOutput_localMap
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_parameter_localMap

section
noncomputable section
namespace QEC.Coding.BDL26NativeFiniteComposition
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
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
namespace Paid
end Paid
private theorem successor_good_ae {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (ν : Measure (StageMaps p n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (StagePresentation p n) J p.t) :
    ∀ᵐ z ∂ν.prod (freshLaw p n),
      IsBoundedDensityLocalMap (StagePresentation p (n+1)) (successor p n z.1 z.2) p.t := by
  filter_upwards [native_random_input_geometry_ae (perturbationOddScale p) n p ν hν]
    with z hz
  exact replacementOutput_localMap p n (state (perturbationOddScale p) n) _
    (state_boundedValence _ n) hz.2.2.1 hz.2.2.2
namespace Decoded
end Decoded
namespace Paid
end Paid
end QEC.Coding.BDL26NativeFiniteComposition
end
end

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ J ∂outputLaw p n, IsBoundedDensityLocalMap (StagePresentation p n) J p.t := by
  induction n with
  | zero =>
    apply (ae_map_iff (measurable_evaluate p 0).aemeasurable
      (measurableSet_boundedDensityLocalMap _ p.t)).mpr
    exact Filter.Eventually.of_forall (fun _ => BDL26RandomSeedEmbedding.seed_parameter_localMap p)
  | succ n ih =>
    rw [outputLaw_succ]
    exact (ae_map_iff (measurable_successor p n).aemeasurable
      (measurableSet_boundedDensityLocalMap _ p.t)).mpr
      (successor_good_ae p n (outputLaw p n) ih)
end QEC.Coding.BDL26NativeFiniteComposition
