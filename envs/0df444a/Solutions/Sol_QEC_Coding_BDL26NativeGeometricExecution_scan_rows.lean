-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.scan_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:44:31.706476+00:00
-- url     : https://prove2.me/submissions/f5db77b2-1cdc-44ee-a426-7803b12efea8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_points_rows
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_scan_actual
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_scan_actual


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
theorem _root_.solution (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n)
    (c : Vertex (Presentation S n) → ℕ) :
    (scanQ S n J hr lambda K
      (SR.rowsFor (SR.indices (SR.count S n)) (SR.encodeSamples S n T)
        (fun a => c (SR.decode S n a)))).1.map (event S n J r) =
      select (localEvent (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K)) (assignment (X := fun _ : Vertex (Presentation S n) => Space) T c) := by
  rw [scan_actual,points_rows]
end QEC.Coding.BDL26NativeGeometricExecution
