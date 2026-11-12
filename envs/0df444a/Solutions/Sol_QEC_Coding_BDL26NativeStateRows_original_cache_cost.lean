-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.original_cache_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:55:27.708849+00:00
-- url     : https://prove2.me/submissions/1d9bc18b-8b08-4fd2-8b31-a094bfa8e3b1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_execute_cost
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_trace_size

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
    (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).operations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        2*(count S n)^2+12*count S n+6+2*m+35*count S n*m ∧
    (executeQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).allocations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        (count S n)^2+2*count S n+2+2*count S n*m := by
  have h := execute_cost S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)
  have hs := original_trace_size S n J r lambda K T m
  rw [hs.1] at h
  have hw := Nat.mul_le_mul_left (count S n) (Nat.mul_le_mul_left 2 hs.2)
  constructor <;> nlinarith [h.1,h.2]
end QEC.Coding.BDL26NativeStateRows
