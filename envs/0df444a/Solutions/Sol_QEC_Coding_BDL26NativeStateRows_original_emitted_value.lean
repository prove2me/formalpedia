-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.original_emitted_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:57:49.251836+00:00
-- url     : https://prove2.me/submissions/93259d86-c7be-4822-9780-83c267f78178

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_emitted_value
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_trace_counters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
open scoped Classical
open QEC.Coding.ProbabilisticConstruction
namespace QEC.Coding.BDL26NativeStateRows
theorem _root_.solution (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    (emittedQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).value=
      (indices (count S n)).map (fun a => (a,assignment (X := fun _ : Vertex (P S n) => Space) (asTable T)
        (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m)
        (decode S n a))) := by
  rw [emitted_value,original_trace_counters]
  rfl
end QEC.Coding.BDL26NativeStateRows
