-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.prefix_assignment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:55:53.438019+00:00
-- url     : https://prove2.me/submissions/ac12f51e-b696-4fc3-9e06-32394746e0a7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_points_rows
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_rows

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
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) (m : ℕ) :
    originalPoints S n (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.rows =
      assignment (X := fun _ : Vertex (Presentation S n) => Space) T (counters (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m) := by
  rw [prefix_rows,points_rows]
end QEC.Coding.BDL26NativeGeometricExecution
