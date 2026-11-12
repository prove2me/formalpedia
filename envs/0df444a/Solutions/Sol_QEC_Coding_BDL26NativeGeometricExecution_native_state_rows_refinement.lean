-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.native_state_rows_refinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:31:35.456841+00:00
-- url     : https://prove2.me/submissions/a5d78e60-1a51-46af-b60e-a39c3650d47e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_rows
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_read
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_trace_counters_original
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_execute_value
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
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.rows =
      (SR.executeQ S n (SR.encodeSamples S n T)
        (supportTrace S n J hr lambda K (SR.encodeSamples S n T) m)).value ∧
    ∀ v : Vertex (Presentation S n),
      (SR.readQ ((SR.decode S n).symm v)
        (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.rows).value =
      (counters (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m v,
        assignment (X := fun _ : Vertex (Presentation S n) => Space) T (counters (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m) v) := by
  refine ⟨?_,prefix_read S n J hr lambda K T m⟩
  rw [prefix_rows,SR.execute_value,trace_counters_original]
end QEC.Coding.BDL26NativeGeometricExecution
