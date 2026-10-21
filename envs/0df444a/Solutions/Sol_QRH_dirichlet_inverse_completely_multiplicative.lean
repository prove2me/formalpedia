-- Prove2me | solution 1 for QRH.dirichlet_inverse_completely_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:07:15.154805+00:00
-- url     : https://prove2.me/submissions/d0f1dde1-3326-484b-85b6-fb9151e03211

import Mathlib
import Definitions.Def_QRH_arith
import Definitions.Def_QRH_sums
import Definitions.Def_QRH_lfun
universe u

open QRH

theorem solution (W : QRHWorld.{u})
    (d : W.E → ℂ)
    (hd_mul : ∀ (a b : W.E), d (W.mul a b) = d a * d b)
    (hd_one : d W.one = 1) :
    ∑ n ∈ W.divs W.one, W.mu n * d n * d (W.coDiv W.one n) = 1
      ∧ ∀ b : W.E, b ≠ W.one →
        ∑ n ∈ W.divs b, W.mu n * d n * d (W.coDiv b n) = 0 := by
  have key : ∀ b : W.E, ∑ n ∈ W.divs b, W.mu n * d n * d (W.coDiv b n) =
      d b * ∑ n ∈ W.divs b, W.mu n := by
    intro b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [mul_assoc, ← hd_mul, W.codiv_mul b n hn]
    ring
  refine ⟨?_, fun b hb => ?_⟩
  · rw [key, hd_one, W.mu_inversion_one, one_mul]
  · rw [key, W.mu_inversion_ne b hb, mul_zero]
