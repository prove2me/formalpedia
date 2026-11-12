-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.nativeOutput_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:33:23.786205+00:00
-- url     : https://prove2.me/submissions/cb15adde-3c79-4374-9ef7-f3cd0fc85ec2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_decoded_table_law
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
    (nativeTableMeasure S n p).map (nativeOutput S n J p) =
      (tableMeasure (Presentation S n) p).map
        (result (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J p) := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  rw [← decoded_table_law S n p,Measure.map_map (measurable_result _ _ _ _ _) hd]
  congr 1
  exact funext (nativeOutput_decoded S n J p)
end QEC.Coding.BDL26NativeGeometricExecution
