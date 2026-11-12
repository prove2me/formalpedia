-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricJointExecution.measurable_joint_nativeOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:31:07.311934+00:00
-- url     : https://prove2.me/submissions/be6c92cc-2683-4ea5-a7b0-fbbc663fa9f1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_native_prefix
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_native_clock
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
private theorem measurable_returned (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    Measurable (fun z : JointInput S n => returned S n z.1 hr lambda K z.2) := by
  have hp : Measurable (fun w : JointInput S n × ℕ =>
      (prefixObservation S n w.1.1 hr lambda K w.1.2 w.2).1) :=
    measurable_from_prod_countable_left
      (fun m => (measurable_native_prefix S n hr lambda K m).fst)
  have hs := hp.comp (measurable_id.prodMk (measurable_native_clock S n hr lambda K))
  apply measurable_pi_lambda
  intro v
  exact ((measurable_pi_apply ((SR.decode S n).symm v)).comp hs).snd
end QEC.Coding.BDL26NativeGeometricJointExecution
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
namespace QEC.Coding.BDL26NativeGeometricJointExecution
theorem _root_.solution (S : OddScale) (n : ℕ)
    {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun z : JointInput S n => nativeOutput S n z.1 p z.2) :=
  measurable_returned S n (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda)
end QEC.Coding.BDL26NativeGeometricJointExecution
