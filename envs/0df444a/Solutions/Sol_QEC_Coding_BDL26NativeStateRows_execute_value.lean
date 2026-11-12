-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.execute_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:48:44.806223+00:00
-- url     : https://prove2.me/submissions/ddd9885d-286a-4ca4-b9cc-b79ad1522279

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_trace_value
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QEC.Coding.BDL26NativeStateRows
theorem _root_.solution (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (executeQ S n T trace).value=
      rowsFor (indices (count S n)) T (traceCounters trace (fun _ => 0)) := by
  change (runFromQ T (initializeQ S n T).value trace).value=_
  rw [initialize_value]
  exact trace_value T _ _ _
end QEC.Coding.BDL26NativeStateRows
