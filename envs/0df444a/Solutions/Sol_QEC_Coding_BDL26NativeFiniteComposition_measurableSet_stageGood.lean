-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.measurableSet_stageGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:04:59.853561+00:00
-- url     : https://prove2.me/submissions/009b9c50-912e-4636-8f1b-8bdfb0827801

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_stageInput
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stageInput
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurableSet_joint_nativeGood
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_joint_nativeOutput

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
    MeasurableSet {z | stageGood p N i z} := by
  have hout : Measurable (fun z : Experiment p N =>
      nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z)) :=
    measurable_comp_pointwise
      (Ω := Experiment p N) (A := JointInput (perturbationOddScale p) i.val)
      (B := Input (perturbationOddScale p) i.val)
      (fun w => nativeOutput (perturbationOddScale p) i.val w.1 p w.2)
      (stagePair p N i) _ (measurable_joint_nativeOutput _ i.val p)
      (measurable_stagePair p N i) (fun _ => rfl)
  exact measurableSet_pullback_pointwise
    (Ω := Experiment p N)
    (A := Input (perturbationOddScale p) i.val × Input (perturbationOddScale p) i.val)
    (fun z => (stageInput p N i z,
      nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z)))
    {w | w.2 ∈ BDL26NativeGeometricAvoidance.NativeGood (perturbationOddScale p) i.val w.1 p}
    (stageGood p N i) ((measurable_stageInput p N i).prodMk hout)
    (measurableSet_joint_nativeGood _ i.val p) (fun _ => Iff.rfl)
end QEC.Coding.BDL26NativeFiniteComposition
