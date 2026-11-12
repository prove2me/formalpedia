-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.native_execution_geometry_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:52:47.771087+00:00
-- url     : https://prove2.me/submissions/55184189-0b62-4054-8584-1b27c1bc17d9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_halts_original
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_encoded_decoded
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_decoded_table_law
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_nativeOutput_decoded
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_measurable_nativeOutput
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_halts_good_ae
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_measurable_result
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyGood_geometry_density
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_KeyGood
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_keyBad
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_decodeTable
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_halts


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace QEC.Coding.BDL26NativeGeometricExecution
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    Measurable (nativeOutput S n J p) ∧
    ∀ᵐ T ∂nativeTableMeasure S n p,
      NativeHalts S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T ∧
      nativeOutput S n J p T ∈ BDL26NativeGeometricAvoidance.NativeGood S n J p ∧
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) J p.lambda (nativeOutput S n J p T))
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) J p.lambda (nativeOutput S n J p T)))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  refine ⟨measurable_nativeOutput S n J p,?_⟩
  have h := halts_good_ae (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) J p hJ (state_boundedValence S n)
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (X := Space) (SR.decode S n)
  have hm : MeasurableSet {T : OriginalTable S n |
      Halts (X := fun _ : Vertex (Presentation S n) => Space) (U S n J (anchorRadius p.m))
        (B S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
      result (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J p T ∈
        KeyGood (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J p} :=
    (measurableSet_halts (X := fun _ : Vertex (Presentation S n) => Space) _ _ (measurableSet_keyBad _ _ _ _ _ _ _)).inter
      ((measurableSet_KeyGood _ _ _ _ _).preimage (measurable_result _ _ _ _ _))
  have hp := (ae_map_iff hd.aemeasurable hm).mp (by
    rw [decoded_table_law S n p]
    exact h)
  filter_upwards [hp] with T hT
  have hh : NativeHalts S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T := by
    rw [← encoded_decoded S n T]
    exact (halts_original S n J _ _ _ _).mpr hT.1
  rw [nativeOutput_decoded]
  exact ⟨hh,hT.2,keyGood_geometry_density (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) J p hJ (state_boundedValence S n) _ hT.2⟩
end QEC.Coding.BDL26NativeGeometricExecution
