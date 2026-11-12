-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricJointExecution.native_random_input_cost_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:36:23.547203+00:00
-- url     : https://prove2.me/submissions/c3167b80-3348-44b8-bbe6-288d963f3545

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_joint_nativeOperationCost

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
theorem _root_.solution (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν] :
    (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) =
      ∫⁻ J, ∫⁻ T, nativeOperationCost S n J (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p ∂ν :=
  lintegral_prod _ (measurable_joint_nativeOperationCost S n (radius_nonneg p)
    p.lambda ((6*p.m+2)*p.lambda)).aemeasurable
end QEC.Coding.BDL26NativeGeometricJointExecution
