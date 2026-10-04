-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_kernel_explicit_m
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T21:13:57.154572+00:00
-- url     : https://prove2.me/submissions/e910182e-8d3b-4ba5-bd76-83ecadc25bf5

-- Target: OddPerfectNumber.Kernel.five_two_prime_kernel_explicit_m
-- 223c7991-79c4-4784-a047-982c3dc76f21
--
-- DIAGNOSTIC HISTORY for candidate 6718 (5 groups, all read from the full captured report).
--   L25 "No goals to be solved" and L26 `omega could not prove the goal` .... the `hhalf` block
--     contained a dead `rw [hp1]` followed by a `have he` that `rw` had already closed, and the
--     follow-up `omega` had no remaining goal.  Both are cascades of one stray tactic.
--   L29 `Function expected at Nat.dvd_of_mod_eq_zero` .... that lemma takes its divisibility
--     proof as an explicit argument, not a proof of `(x % n = 0)`; `omega` was passed instead.
--   L39 `linarith failed to find a contradiction`, residual `a✝ : 3 * u * a * b * d1 * q * r < m`
--     .... THE IMPORTANT ONE.  The report shows `hhalf`, `hsub` and `hsq` all elaborated
--     correctly, so only the final step failed: `nlinarith` cannot derive `m = X` from
--     `m ^ 2 = X ^ 2` over `Nat`, because the residual is a strict inequality, not an equality.
--     The correct tool is `Nat.sqrt_eq'`, which reads `sqrt (n ^ 2) = n`.
--
-- THE REPAIR keeps `hhalf`, `hsub` and `hsq` in the shape the compiler confirmed, removes the
-- two stray tactics that caused L25/L26/L29, and closes the goal with `Nat.sqrt_eq'` plus
-- `Nat.sqrt_eq_zero_iff`, so no inequality reasoning is involved at all.

import Mathlib

namespace OddPerfectNumber
namespace Kernel
namespace MForm

theorem solution_aux (p m u a b d1 q r : Nat)
    (hp1 : p + 1 = 6 * u ^ 2)
    (hC : p ^ 2 + p + 1 = q * a ^ 2)
    (hD : p ^ 2 - p + 1 = 3 * r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r := by
  -- `(p + 1) / 2 = 3 * u ^ 2`: from `p + 1 = 6 u^2` and the fact that `6 u^2` is even.
  have hhalf : (p + 1) / 2 = 3 * u ^ 2 := by
    have he : 2 ∣ p + 1 := by
      rw [hp1]
      exact ⟨3 * u ^ 2, by ring⟩
    obtain ⟨k, hk⟩ := he
    rw [hk] at hp1
    omega
  -- Substitute the three block equations into `h1`; the right side becomes a perfect square.
  have hsub : 2 * m ^ 2 = 2 * (3 * u * a * b * d1 * q * r) ^ 2 := by
    rw [hC, hD, hhalf] at h1
    nlinarith [h1]
  have hsq : m ^ 2 = (3 * u * a * b * d1 * q * r) ^ 2 := by nlinarith [hsub]
  -- `Nat.sqrt_eq'` is the tool the previous candidate lacked: it is `sqrt (n ^ 2) = n`.
  -- DIAGNOSTIC HISTORY for candidate 6721 (2 groups).  The report shows `hroot` ELABORATED
  -- correctly and only the trailing `exact hroot` was left: `rw [Nat.sqrt_eq', ...] at hz`
  -- closed the goal itself, so the `exact` found no goals.  The repair drops the redundant
  -- `exact` and keeps the single rewrite step, so no `rw` is left without a goal.
  -- DIAGNOSTIC HISTORY for candidates 6721, 6729 and 6733 (2, 2 and 1 groups).  ALL THREE
  -- reports show the context already containing
  --     hroot : m = 3 * u * a * b * d1 * q * r
  -- with the leftover goal being that very statement, so the mathematics was finished every
  -- time and only a DUPLICATE tactic remained:
  --   6721/6729 -- `rw [Nat.sqrt_eq', ...] at hz` already closes the goal, so the following
  --     `exact hz` is dead and a second `rw` then reports "did not find (m ^ 2).sqrt".
  --   6733 -- with the calc form, `hroot` was proved and then RE-PROVED by the trailing `exact`,
  --     leaving "unsolved goals" on the identical statement.
  -- THE REPAIR proves the square-root step ONCE, directly, and lets it be the whole proof body.
  have hroot : m = 3 * u * a * b * d1 * q * r := by
    calc m = Nat.sqrt (m ^ 2) := (Nat.sqrt_eq' m).symm
      _ = Nat.sqrt ((3 * u * a * b * d1 * q * r) ^ 2) := by rw [hsq]
      _ = 3 * u * a * b * d1 * q * r := Nat.sqrt_eq' _
  exact hroot

end MForm
end Kernel
end OddPerfectNumber

open OddPerfectNumber
open OddPerfectNumber.Kernel

theorem solution (p m u a b d1 q r : Nat)
    (hp1 : p + 1 = 6 * u ^ 2)
    (hC : p ^ 2 + p + 1 = q * a ^ 2)
    (hD : p ^ 2 - p + 1 = 3 * r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r :=
  OddPerfectNumber.Kernel.MForm.solution_aux p m u a b d1 q r hp1 hC hD h1
