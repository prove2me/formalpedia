-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricExecution.returned_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T11:16:44.069729+00:00
-- url     : https://prove2.me/submissions/d9ddfb77-5010-42e7-afef-55a7a3904fd7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_assignment
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_haltTime_original

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
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) :
    returned S n J hr lambda K (SR.encodeSamples S n T) =
      output (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T := by
  unfold returned
  rw [haltTime_original,prefix_assignment]
  rfl
end QEC.Coding.BDL26NativeGeometricExecution
