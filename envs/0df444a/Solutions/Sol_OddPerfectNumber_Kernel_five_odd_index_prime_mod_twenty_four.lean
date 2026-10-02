-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_odd_index_prime_mod_twenty_four
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T11:01:41.2134+00:00
-- url     : https://prove2.me/submissions/05a9161a-9f9f-43f0-9da2-144f73537177

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.five_odd_index_prime_mod_twenty_four
--          3d16e812-9942-4647-b9fd-4c6ef11ed954
--
-- If an odd index prime `q` is the odd-multiplicity factor of a cyclotomic block
-- that is `7 (mod 8)` and `1 (mod 3)`, then `q = 7 (mod 24)`.
--
-- DIAGNOSTIC HISTORY FOR THIS REVISION.
-- Candidates 6283 (5 groups) and 6290 (4 groups) both returned CE, and every group was
-- a `rw` that failed to find its pattern. The cause is a single shape mistake repeated
-- in four places: the proof `obtains ⟨k, rfl⟩ := ha`, so `a` is REPLACED by `2 * k + 1`
-- everywhere, and `hfactor : N = q * a ^ 2` therefore still mentions `a`. Rewriting with
-- `[hfactor]` in a goal that no longer mentions `a`, or rewriting the goal `q % 8 = 7`
-- which never contains `N`, leaves `N` unmatched:
--   * 6290 E01 `rw [← hfactor]` on goal `q % 8 = 7` reported the pattern
--     `q * (2 * k + 1) ^ 2` absent from the target `q % 8 = 7`: the rewrite was aimed
--     at the wrong goal.
--   * 6290 E03/E04 `rw [hfactor]` reported the pattern `N` absent from
--     `q * (2 * k + 1) ^ 2 % 3 = 0` and `q % 3 = 1`.
--   * 6290 E02 was a cascade: `Nat.pow_mod` on `(2 * k + 1) ^ 2 % 3` with the residue
--     hypothesis produced the spurious goal `q % 3 * 0 % 3 = 0`.
--
-- THE REPAIR keeps `a` abstract (no `rfl` substitution) and works with `N` on the left
-- of each congruence, exactly as the supplied reference `lean/11_index_prime_mod_three.lean`
-- does: substitute `hfactor` INTO the given remainder facts, so `N` is replaced by
-- `q * a ^ 2`, and then reason about `a` modulo 8 and 3 by an explicit four-case and
-- two-case split. `N` never appears on the right of a rewrite, so no pattern is missed.
import Mathlib

namespace OddPerfectNumber
namespace Kernel
namespace Mod24B

theorem solution_aux (N q a : Nat)
    (hN8 : N % 8 = 7) (hfactor : N = q * a ^ 2) (ha : Odd a)
    (hN3 : N % 3 = 1) :
    q % 24 = 7 := by
  -- `a` odd means `a = 2 * k + 1`, and `Nat.even_mul_succ_self` exhibits
  -- `k * (k + 1) = j + j` for the `8`-divisibility of the square.
  obtain ⟨k, hk⟩ := ha
  rw [hk] at hfactor
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  -- `(2 * k + 1)^2 = 8 * j + 1`, hence `(2 * k + 1)^2 % 8 = 1`.
  have hsq8 : ((2 * k + 1) ^ 2) % 8 = 1 := by
    have h : (2 * k + 1) ^ 2 = 8 * j + 1 := by nlinarith [hj]
    omega
  -- MOD 8: push `hfactor` into `hN8` so `N` is replaced by `q * (2 * k + 1)^2`, then
  -- use `Nat.mul_mod` with the square residue.
  have hprod8 : (q * (2 * k + 1) ^ 2) % 8 = 7 := by
    rw [← hfactor]
    exact hN8
  rw [Nat.mul_mod, hsq8] at hprod8
  have hq8 : q % 8 = 7 := by omega
  -- MOD 3: `N % 3 = 1` means `3 ∤ N`, so `3 ∤ a`; then `a^2 = 1 (mod 3)` and `q = 1 (mod 3)`.
  have hprod3 : (q * (2 * k + 1) ^ 2) % 3 = 1 := by
    rw [← hfactor]
    exact hN3
  have hna : (2 * k + 1) % 3 ≠ 0 := by
    intro hz
    rw [Nat.mul_mod, Nat.pow_mod, hz, Nat.zero_mod] at hprod3
    omega
  have hcases : (2 * k + 1) % 3 = 1 ∨ (2 * k + 1) % 3 = 2 := by omega
  have hq3 : q % 3 = 1 := by
    rcases hcases with h | h
    · rw [Nat.mul_mod, Nat.pow_mod, h] at hprod3
      omega
    · rw [Nat.mul_mod, Nat.pow_mod, h] at hprod3
      omega
  -- CRT: `q = 7 (mod 8)` and `q = 1 (mod 3)` give `q = 7 (mod 24)`.
  omega

end Mod24B
end Kernel
end OddPerfectNumber

open OddPerfectNumber
open OddPerfectNumber.Kernel

theorem solution (N q a : Nat)
    (hN8 : N % 8 = 7) (hfactor : N = q * a ^ 2) (ha : Odd a)
    (hN3 : N % 3 = 1) :
    q % 24 = 7 :=
  OddPerfectNumber.Kernel.Mod24B.solution_aux N q a hN8 hfactor ha hN3
