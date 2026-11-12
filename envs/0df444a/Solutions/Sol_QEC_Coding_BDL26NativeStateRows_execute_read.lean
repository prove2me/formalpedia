-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.execute_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:54:44.948233+00:00
-- url     : https://prove2.me/submissions/b035d718-e65c-427f-9c74-c62f4b11e8d3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_indices_complete
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_read_rowsFor
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_execute_value

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
    (trace : List (List (Index S n))) (a : Index S n) :
    (readQ a (executeQ S n T trace).value).value=
      (traceCounters trace (fun _ => 0) a,T (a,traceCounters trace (fun _ => 0) a)) := by
  rw [execute_value]
  exact read_rowsFor T _ _ a (indices_complete _ a)
end QEC.Coding.BDL26NativeStateRows
