-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_step_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:57.603918+00:00
-- url     : https://prove2.me/submissions/7aa48725-ebf9-4684-bcaf-b049b9961e6e

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D n : ℕ) (a : Fin (D + 1) → ℕ) (ha : a ∈ Finset.Nat.antidiagonalTuple (D + 1) n) :
    0 ≤ -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) ∧
      -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) ≤ Real.log ((n : ℝ) + D + 1) := by
  have ha' := Finset.Nat.mem_antidiagonalTuple.mp ha
  have h0 : a 0 ≤ n := by
    rw [← ha']
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (a i)) (Finset.mem_univ 0)
  have h0' : (a 0 : ℝ) ≤ n := by exact_mod_cast h0
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have ha0 : (0 : ℝ) ≤ a 0 := Nat.cast_nonneg _
  have hden : (0 : ℝ) < (n : ℝ) + D + 1 := by positivity
  have hpos : (0 : ℝ) < (a 0 + 1 : ℝ) / ((n : ℝ) + D + 1) := by positivity
  have hle1 : (a 0 + 1 : ℝ) / ((n : ℝ) + D + 1) ≤ 1 := by
    have hnum : (a 0 + 1 : ℝ) ≤ (n : ℝ) + D + 1 := by linarith
    first
      | exact (div_le_one hden).mpr hnum
      | exact (div_le_one₀ hden).mpr hnum
      | exact div_le_one_of_le₀ hnum hden.le
  constructor
  · have := Real.log_nonpos hpos.le hle1
    linarith
  · rw [Real.log_div (by positivity) (by positivity)]
    have : 0 ≤ Real.log ((a 0 : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith
end ReciprocityTheory.GeometryOfNumbersTheory
