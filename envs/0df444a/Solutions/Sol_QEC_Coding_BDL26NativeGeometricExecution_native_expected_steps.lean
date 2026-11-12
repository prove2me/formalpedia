-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.native_expected_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:16:50.956862+00:00
-- url     : https://prove2.me/submissions/1a09eb8a-fe28-427b-9b34-bddcb7508491

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_totalSteps_original
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_encoded_decoded
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_decoded_table_law
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_expected_steps_explicit_finite
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_measurableSet_keyBad
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_decodeTable
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_totalSteps
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (∫⁻ T, nativeTotalSteps S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T
      ∂nativeTableMeasure S n p) ≤
      ENNReal.ofReal ((Fintype.card (Triangle (Presentation S n)) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) ∧
    ENNReal.ofReal ((Fintype.card (Triangle (Presentation S n)) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) < ∞ := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  have he : nativeTotalSteps S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) =
      totalSteps (X := fun _ : Vertex (Presentation S n) => Space) (U S n J (anchorRadius p.m))
        (B S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) ∘ decodedTable S n := by
    funext T
    have h := totalSteps_original S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) (decodedTable S n T)
    rw [encoded_decoded] at h
    exact h
  have hi : (∫⁻ T, nativeTotalSteps S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p) =
      ∫⁻ T, totalSteps (X := fun _ : Vertex (Presentation S n) => Space) (U S n J (anchorRadius p.m))
        (B S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
        ∂tableMeasure (Presentation S n) p := by
    rw [he,← decoded_table_law S n p]
    exact (lintegral_map
      (measurable_totalSteps (X := fun _ : Vertex (Presentation S n) => Space) _ _ (measurableSet_keyBad _ _ _ _ _ _ _)) hd).symm
  rw [hi]
  exact expected_steps_explicit_finite (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) J p hJ (state_boundedValence S n)
end QEC.Coding.BDL26NativeGeometricExecution
