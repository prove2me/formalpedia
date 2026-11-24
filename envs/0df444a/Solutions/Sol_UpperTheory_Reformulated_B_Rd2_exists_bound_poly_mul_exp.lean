-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Rd2.exists_bound_poly_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:09.511578+00:00
-- url     : https://prove2.me/submissions/f2b29b6d-e899-41ec-9078-f225a209ce74

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsBoundPolyMulExpAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Rd2
theorem _root_.solution :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    linarith [Real.add_one_le_exp r]
  have h2 : (N : ℝ) * r + -(c * r ^ 2) ≤ (N : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
  calc (1 + r) ^ N * Real.exp (-(c * r ^ 2))
      ≤ Real.exp ((N : ℝ) * r) * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ 2)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.mpr h2
end UpperTheory.Reformulated.B.Rd2
