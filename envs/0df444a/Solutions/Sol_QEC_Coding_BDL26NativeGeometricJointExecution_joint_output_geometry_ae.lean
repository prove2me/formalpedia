-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricJointExecution.joint_output_geometry_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:35:17.785211+00:00
-- url     : https://prove2.me/submissions/42290b65-dc99-41e4-90db-d94f3a7b325e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurableSet_native_halts
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_joint_nativeOutput
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurableSet_joint_nativeGood
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyGood_geometry_density
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_native_execution_geometry_ae
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_boundedDensityLocalMap

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
private theorem measurableSet_joint_success (S : OddScale) (n : ℕ)
    {L : ℝ} (p : GeometricParameters L) :
    MeasurableSet {z : JointInput S n |
      IsBoundedDensityLocalMap (Presentation S n) z.1 p.t ∧
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 ∧
      nativeOutput S n z.1 p z.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n z.1 p} := by
  have hI : MeasurableSet {z : JointInput S n |
      IsBoundedDensityLocalMap (Presentation S n) z.1 p.t} :=
    (measurableSet_boundedDensityLocalMap (Presentation S n) p.t).preimage measurable_fst
  have hH : MeasurableSet {z : JointInput S n |
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2} :=
    measurableSet_native_halts S n (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda)
  have hm : Measurable (jointOutput S n p) :=
    measurable_fst.prodMk (measurable_joint_nativeOutput S n p)
  have he : {z : JointInput S n |
      IsBoundedDensityLocalMap (Presentation S n) z.1 p.t ∧
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 ∧
      nativeOutput S n z.1 p z.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n z.1 p} =
      {z : JointInput S n | IsBoundedDensityLocalMap (Presentation S n) z.1 p.t} ∩
        ({z : JointInput S n |
          NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2} ∩
          (jointOutput S n p) ⁻¹' {y : Input S n × Input S n |
            y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p}) := by
    ext z
    rfl
  rw [he]
  exact hI.inter (hH.inter ((measurableSet_joint_nativeGood S n p).preimage hm))
private theorem joint_success_ae (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    ∀ᵐ z ∂ν.prod (nativeTableMeasure S n p),
      IsBoundedDensityLocalMap (Presentation S n) z.1 p.t ∧
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 ∧
      nativeOutput S n z.1 p z.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n z.1 p := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_joint_success S n p)).mpr
  filter_upwards [hν] with J hJ
  filter_upwards [(native_execution_geometry_ae S n J p hJ).2] with T hT
  exact ⟨hJ,hT.1,hT.2.1⟩
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
theorem _root_.solution (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    ∀ᵐ y ∂(ν.prod (nativeTableMeasure S n p)).map (jointOutput S n p),
      IsBoundedDensityLocalMap (Presentation S n) y.1 p.t ∧
      y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p ∧
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) y.1 p.lambda y.2)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ center, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) y.1 p.lambda y.2))
        (Metric.closedBall center 1)).card : ℝ) ≤ triangleDensityBound := by
  have hm : Measurable (jointOutput S n p) :=
    measurable_fst.prodMk (measurable_joint_nativeOutput S n p)
  have hs : MeasurableSet {y : Input S n × Input S n |
      IsBoundedDensityLocalMap (Presentation S n) y.1 p.t ∧
      y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p} :=
    ((measurableSet_boundedDensityLocalMap (Presentation S n) p.t).preimage measurable_fst).inter
      (measurableSet_joint_nativeGood S n p)
  have hg : ∀ᵐ y ∂(ν.prod (nativeTableMeasure S n p)).map (jointOutput S n p),
      IsBoundedDensityLocalMap (Presentation S n) y.1 p.t ∧
      y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p := by
    apply (ae_map_iff hm.aemeasurable hs).mpr
    filter_upwards [joint_success_ae S n p ν hν] with z hz
    exact ⟨hz.1,hz.2.2⟩
  filter_upwards [hg] with y hy
  exact ⟨hy.1,hy.2,keyGood_geometry_density (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) y.1 p hy.1 (state_boundedValence S n) _ hy.2⟩
end QEC.Coding.BDL26NativeGeometricJointExecution
