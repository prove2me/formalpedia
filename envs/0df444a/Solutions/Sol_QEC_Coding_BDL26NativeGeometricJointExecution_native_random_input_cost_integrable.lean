-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricJointExecution.native_random_input_cost_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:35:26.045185+00:00
-- url     : https://prove2.me/submissions/e646656c-2348-45a8-b7e8-15b8789e562e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_joint_nativeOperationCost
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_random_input_total_cost

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
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) < ∞ ∧
    Integrable (fun z : JointInput S n =>
      (nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) z.2).toReal) (ν.prod (nativeTableMeasure S n p)) := by
  have hf : (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) < ∞ :=
    (native_random_input_total_cost S n p ν hν).trans_lt (ENNReal.natCast_lt_top _)
  refine ⟨hf,?_⟩
  apply integrable_toReal_of_lintegral_ne_top
  · exact (measurable_joint_nativeOperationCost S n (radius_nonneg p)
      p.lambda ((6*p.m+2)*p.lambda)).aemeasurable
  · exact ne_of_lt hf
end QEC.Coding.BDL26NativeGeometricJointExecution
