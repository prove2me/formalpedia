-- Prove2me | solution 1 for Sendov.t3_mul_Q_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:49.861507+00:00
-- url     : https://prove2.me/submissions/e86ea235-a95b-4e33-afc2-691eac50c3b9

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Theorems.Thm_Sendov_quad_pow

set_option autoImplicit false
open Sendov
open MeasureTheory Finset
namespace Sendov
theorem _root_.solution (n : ℕ) (α t : ℝ) (k : ℕ) :
    t ^ 3 * Q n α t ^ k
      = ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
            * t ^ (2 * i - l + 3) := by
  have hQ : Q n α t = 1 + (-2 * c n α) * t + A n α * t ^ 2 := by simp only [Q]; ring
  rw [hQ, quad_pow, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ i := Nat.lt_succ_iff.1 (mem_range.1 hl)
  have hexp : 3 + (2 * i - l) = 2 * i - l + 3 := by omega
  calc t ^ 3 * (((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
        * t ^ (2 * i - l))
      = ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
          * (t ^ 3 * t ^ (2 * i - l)) := by ring
    _ = _ := by rw [← pow_add, hexp]
end Sendov
