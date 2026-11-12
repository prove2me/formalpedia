-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.trace_labels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:53:27.170197+00:00
-- url     : https://prove2.me/submissions/c5dea1bf-d781-415f-a72c-244132811210

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_refresh_labels
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (R : Rows A) (trace : List (List A)) :
    (runFromQ T R trace).value.map Prod.fst=R.map Prod.fst := by
  induction trace generalizing R with
  | nil => rfl
  | cons U trace ih => exact (ih _).trans (refresh_labels T U R)
end QEC.Coding.BDL26NativeStateRows
