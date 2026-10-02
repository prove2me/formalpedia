-- Prove2me | solution 1 for OddPerfectNumber.Kernel.three_val_second_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T11:02:11.57697+00:00
-- url     : https://prove2.me/submissions/93eb4692-af72-4826-a18b-f0a66c5d69f0

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.three_val_second_cyclotomic
--          a3a28b8c-38f4-4272-bc2b-187c3f99f194
--
-- When `p = 2 (mod 3)` the second cyclotomic block `p^2 - p + 1` is divisible by
-- `3` but not by `9`.
--
-- DIAGNOSTIC HISTORY FOR THIS REVISION.
-- Candidates 6286, 6294, 6296, 6297 all returned CE in the SAME place, and all four
-- failures share one cause: the proof tried to transport `p^2 - p + 1` to
-- `p^2 + 2 * p + 1` (which differ by `3 * p`) and then take a `%` of the difference.
--   * 6296 used `(Nat.modEq_iff_dvd' hle).mp`, but `.mp` CONSUMES the congruence and
--     PRODUCES the divisibility, so it supplied `?m | b - a` where the goal was the
--     `%` equation: exactly the direction error the CE reported.
--   * 6297 used `.mpr` (the correct direction) but then wrote `dvd_mul_right 3 p 3`.
--     `Nat.dvd_mul_right : a | a * b` is not a function, so the extra arguments are a
--     spurious application.
--   * Even with both fixed, the subgoal is `3 | (p^2 + 2 * p + 1) - (p^2 - p + 1)`,
--     and the `omega` proving that difference failed, because it contains TRUNCATED
--     `Nat` subtraction: the reported context was the useless fresh atom
--     `b := (p^2 + 2 * p + 1 - (p^2 - p + 1))`.
-- This is precisely the documented `pattern.avoid-nat-subtraction` trap.
--
-- THE REPAIR: never let a truncated `Nat` subtraction meet `omega` or `%`.  Substitute
-- the residue form `p = 3 * k + 2` FIRST, so the block becomes an ordinary
-- polynomial with no subtraction at all.  This is the shape of the reference helper
-- `opn_D_mod_nine_of_p_two_mod_three`, and it makes every residual goal linear in `k`.
import Mathlib

namespace OddPerfectNumber
namespace Kernel
namespace ThreeC2

theorem solution {p : Nat} (hp4 : 4 <= p) (hp3 : p % 3 = 2) :
    (3 : Nat) ∣ p ^ 2 - p + 1 ∧ ¬ (9 : Nat) ∣ p ^ 2 - p + 1 := by
  -- `p % 3 = 2` is exactly `p = 3 * k + 2` for some `k`.
  obtain ⟨k, hk⟩ : ∃ k : Nat, p = 3 * k + 2 :=
    ⟨p / 3, by omega⟩
  -- `omega` cannot linearise a `pow`, so `p ^ 2` is supplied as an OPAQUE atomic
  -- hypothesis proved by `ring` after the substitution.  Candidate 6311 E01 reported
  -- the useless fresh atom `c := (3 * k + 2) ^ 2`, which is exactly this failure.
  have hsq : p ^ 2 = 9 * (k * k) + 12 * k + 4 := by
    rw [hk]
    ring
  -- `1 <= p` makes the truncated subtraction `p ^ 2 - p + 1` non-truncating, and then
  -- `omega` reads the whole identity off `hk` and `hsq`.
  have hp1 : 1 <= p := by omega
  have hform : p ^ 2 - p + 1 = 9 * (k * k + k) + 3 := by
    omega
  -- `3 ∣ ...` is immediate from `hform`.
  refine ⟨by rw [hform]; omega, ?_⟩
  intro h9
  -- `9 ∣ 9 * (k * k + k) + 3` would force the remainder modulo `9` to be `0`, but the
  -- block is plainly `3 (mod 9)`.  Candidate 6311 E02 was a wrong use of
  -- `Nat.mul_eq_right`, which is not available here; `Nat.dvd_iff_mod_eq_zero` is the
  -- idiom the sibling target `three_val_first_cyclotomic` already proved remotely.
  rw [hform] at h9
  have h9' : (9 * (k * k + k) + 3) % 9 = 0 :=
    (@Nat.dvd_iff_mod_eq_zero 9 (9 * (k * k + k) + 3)).mp h9
  omega

end ThreeC2
end Kernel
end OddPerfectNumber

theorem solution {p : Nat} (hp4 : 4 <= p) (hp3 : p % 3 = 2) :
    (3 : Nat) ∣ p ^ 2 - p + 1 ∧ ¬ (9 : Nat) ∣ p ^ 2 - p + 1 :=
  OddPerfectNumber.Kernel.ThreeC2.solution hp4 hp3
