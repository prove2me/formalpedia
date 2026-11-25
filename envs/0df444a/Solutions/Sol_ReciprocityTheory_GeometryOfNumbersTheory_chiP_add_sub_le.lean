-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiP_add_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:04:31.72536+00:00
-- url     : https://prove2.me/submissions/4825d96c-7136-40d0-978f-8b35ea7b1979

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_powLog_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Topology Asymptotics
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D : ℕ) (C : ℝ)
    (hC : ∀ n : ℕ, 1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1))
    (k n : ℕ) (hn : 1 ≤ n) :
    chiP D (n + k) - chiP D n ≤
      ∑ j ∈ Finset.range k, |C| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 := hC (n + k) (by omega)
    have h2 : C * (((n + k : ℕ) : ℝ) ^ D) * Real.log (((n + k : ℕ) : ℝ) + 1) ≤
        |C| * (((n + k : ℕ) : ℝ) ^ D * Real.log (((n + k : ℕ) : ℝ) + 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (powLog_nonneg D (n + k))
    have h3 : chiP D (n + (k + 1)) = chiP D (n + k + 1) := by rw [Nat.add_assoc]
    rw [h3]
    linarith
end ReciprocityTheory.GeometryOfNumbersTheory
