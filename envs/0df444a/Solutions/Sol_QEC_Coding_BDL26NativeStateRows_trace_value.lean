-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.trace_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:42:56.132052+00:00
-- url     : https://prove2.me/submissions/3fd96d82-f19b-4f30-9f9f-24de8c8b7dd6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_refresh_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QEC.Coding.BDL26NativeStateRows
theorem _root_.solution {A : Type*} [DecidableEq A] (T : Samples A)
    (L : List A) (trace : List (List A)) (c : A → ℕ) :
    (runFromQ T (rowsFor L T c) trace).value=rowsFor L T (traceCounters trace c) := by
  induction trace generalizing c with
  | nil => rfl
  | cons U trace ih =>
      change (runFromQ T (refreshQ T U (rowsFor L T c)).value trace).value=_
      rw [refresh_value]
      exact ih _
end QEC.Coding.BDL26NativeStateRows
