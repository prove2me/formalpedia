-- Prove2me | solution 1 for QEC.Coding.BDL26NativeFiniteComposition.measurable_jointObservation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:31:08.476105+00:00
-- url     : https://prove2.me/submissions/3bd0f2cc-04f5-4c7e-a367-d71eb674a8ad

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurable_jointStageCost
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_measurable_prefixObservation
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_jointStageCost
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurableSet_native_halts
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_joint_nativeOutput
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_native_clock
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_native_selection


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
    Measurable (jointObservation p n) := by
  have hchoice (m : ℕ) :=
    (measurable_native_selection (perturbationOddScale p) n (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda) m).fst
  exact measurable_fst.prodMk
    ((measurable_pi_lambda _ (fun time => Paid.measurable_prefixObservation _ n
      (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) time)).prodMk
    ((measurable_pi_lambda _ hchoice).prodMk
    ((Measurable.ite (BDL26NativeGeometricJointExecution.measurableSet_native_halts _ n
      (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda)) measurable_const measurable_const).prodMk
    ((BDL26NativeGeometricJointExecution.measurable_native_clock _ n (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda)).prodMk
    ((measurable_joint_nativeOutput _ n p).prodMk
    ((measurable_nativePerturbed p n).prodMk
    ((measurable_successor p n).prodMk (measurable_jointStageCost p n))))))))
end QEC.Coding.BDL26NativeFiniteComposition
