-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.emitted_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:59:20.699215+00:00
-- url     : https://prove2.me/submissions/825140d9-8c53-4028-a0f4-79c6f9d7b49f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_emit_value
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
    (trace : List (List (Index S n))) :
    (emittedQ S n T trace).value=(indices (count S n)).map
      (fun a => (a,T (a,traceCounters trace (fun _ => 0) a))) := by
  change (emitQ (executeQ S n T trace).value).value=_
  rw [execute_value]
  exact emit_value _ _ _
end QEC.Coding.BDL26NativeStateRows
