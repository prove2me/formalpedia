-- Prove2me | solution 1 for Sendov.quad_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:11.718935+00:00
-- url     : https://prove2.me/submissions/087ff959-c268-48f4-b4ce-6bdcb63f0275

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments

set_option autoImplicit false
open Sendov
open MeasureTheory Finset
namespace Sendov
theorem _root_.solution (b d t : ℝ) (k : ℕ) :
    (1 + b * t + d * t ^ 2) ^ k
      = ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * t ^ (2 * i - l) := by
  rw [show (1 + b * t + d * t ^ 2) = (b * t + d * t ^ 2) + 1 by ring, add_pow]
  refine sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, add_pow, sum_mul]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ i := Nat.lt_succ_iff.1 (mem_range.1 hl)
  have hexp : l + 2 * (i - l) = 2 * i - l := by omega
  rw [mul_pow, mul_pow, ← pow_mul]
  calc b ^ l * t ^ l * (d ^ (i - l) * t ^ (2 * (i - l))) * (i.choose l : ℝ) * (k.choose i : ℝ)
      = ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * (t ^ l * t ^ (2 * (i - l))) := by
        ring
    _ = ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * t ^ (2 * i - l) := by
        rw [← pow_add, hexp]
end Sendov
