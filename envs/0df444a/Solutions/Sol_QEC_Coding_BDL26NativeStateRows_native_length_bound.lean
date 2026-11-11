-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.native_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:37:27.608814+00:00
-- url     : https://prove2.me/submissions/8faeebcc-ec35-4d89-ad12-fc7a967f0a93

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_retained_space


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QEC.Coding.BDL26NativeStateRows
theorem _root_.solution (S : OddScale) (n : ℕ) :
    count S n≤(n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15 := by
  have h := BDL26NativePresentationGenerator.retained_space S n
  unfold BDL26NativePresentationGenerator.outputRecords at h
  change (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices.length≤_
  omega
end QEC.Coding.BDL26NativeStateRows
