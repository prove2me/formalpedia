-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.measurableSet_stageHalts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:04:45.485198+00:00
-- url     : https://prove2.me/submissions/4e0a3f52-f185-4b19-8e17-9fc42a5a54f5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurableSet_native_halts

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
private theorem measurableSet_pullback_pointwise {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (f : Ω → A) (s : Set A) (out : Ω → Prop)
    (hf : Measurable f) (hs : MeasurableSet s)
    (he : ∀ z, out z ↔ f z ∈ s) : MeasurableSet {z | out z} := by
  have h : {z | out z} = f ⁻¹' s := Set.ext he
  rw [h]
  exact hs.preimage hf
namespace Paid
end Paid
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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) :
    MeasurableSet {z | stageHalts p N i z} := by
  exact measurableSet_pullback_pointwise
    (Ω := Experiment p N) (A := JointInput (perturbationOddScale p) i.val)
    (stagePair p N i)
    {w | NativeHalts (perturbationOddScale p) i.val w.1 (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda) w.2}
    (stageHalts p N i) (measurable_stagePair p N i)
    (BDL26NativeGeometricJointExecution.measurableSet_native_halts _ i.val (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda)) (fun _ => Iff.rfl)
end QEC.Coding.BDL26NativeFiniteComposition
