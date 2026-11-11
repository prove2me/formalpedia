-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.trace_counters_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:21:55.011956+00:00
-- url     : https://prove2.me/submissions/c6e86578-3fb3-42f0-bbf4-5ccbbcff482f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QEC.Coding.BDL26NativeStateRows
theorem _root_.solution {A : Type*} [DecidableEq A]
    (left right : List (List A)) (c : A → ℕ) :
    traceCounters (left++right) c=traceCounters right (traceCounters left c) := by
  induction left generalizing c with
  | nil => rfl
  | cons U left ih => exact ih _
end QEC.Coding.BDL26NativeStateRows
