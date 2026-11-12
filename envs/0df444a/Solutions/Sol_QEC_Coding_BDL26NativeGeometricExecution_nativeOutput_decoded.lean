-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.nativeOutput_decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:22:28.951762+00:00
-- url     : https://prove2.me/submissions/c9b49357-6096-4eca-9c7a-2a647231bf5d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_returned_original
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_encoded_decoded
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective


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
    (T : NativeTable S n) : nativeOutput S n J p T =
      result (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J p (decodedTable S n T) := by
  have h := returned_original S n J (radius_nonneg p) p.lambda
    ((6*p.m+2)*p.lambda) (decodedTable S n T)
  rw [encoded_decoded] at h
  exact h
end QEC.Coding.BDL26NativeGeometricExecution
