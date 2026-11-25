-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.bI_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:05.847814+00:00
-- url     : https://prove2.me/submissions/44f81e9d-b09e-472d-b09c-d71dde0e8126

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory
open scoped ComplexOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (i j : ℕ) : ((j : ℝ) + 1) * betaNatInt (i + 1) j = ((i : ℝ) + 1) * betaNatInt i (j + 1) := by
  unfold betaNatInt
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => x ^ (i + 1)) (((i:ℝ) + 1) * x ^ i) x := by
    intro x _
    simpa using hasDerivAt_pow (i + 1) x
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => -(1 - x) ^ (j + 1)) (((j:ℝ) + 1) * (1 - x) ^ j) x := by
    intro x _
    have h2 := (((hasDerivAt_id x).const_sub 1).pow (j + 1)).neg
    refine h2.congr_deriv ?_
    first
      | (simp only [id, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]; ring)
      | (simp; ring)
      | simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have e1 : ∫ x in (0:ℝ)..1, ((j:ℝ) + 1) * (x ^ (i + 1) * (1 - x) ^ j) =
      ∫ x in (0:ℝ)..1, x ^ (i + 1) * (((j:ℝ) + 1) * (1 - x) ^ j) := by
    congr 1; funext x; ring
  have e2 : ∫ x in (0:ℝ)..1, ((i:ℝ) + 1) * (x ^ i * (1 - x) ^ (j + 1)) =
      -∫ x in (0:ℝ)..1, ((i:ℝ) + 1) * x ^ i * (-(1 - x) ^ (j + 1)) := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, e1, e2, hparts]
  simp
end ReciprocityTheory.GeometryOfNumbersTheory
