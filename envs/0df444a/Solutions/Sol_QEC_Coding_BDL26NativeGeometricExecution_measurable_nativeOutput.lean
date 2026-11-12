-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.measurable_nativeOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:29:21.548427+00:00
-- url     : https://prove2.me/submissions/2d85d617-073c-4f28-a6b3-03c1754ae75b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_nativeOutput_decoded
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_measurable_result
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_decodeTable


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
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L) :
    Measurable (nativeOutput S n J p) := by
  have he : nativeOutput S n J p =
      result (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J p ∘
        decodedTable S n := funext (nativeOutput_decoded S n J p)
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  rw [he]
  exact (measurable_result _ _ _ _ _).comp hd
end QEC.Coding.BDL26NativeGeometricExecution
