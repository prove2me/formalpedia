-- Prove2me | solution 1 for OddPerfectNumber.Kernel.isSq_of_sq_mul_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T15:04:15.971813+00:00
-- url     : https://prove2.me/submissions/08d240b7-65ce-4e0f-a6bd-c93bc681961f

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Cancelling an explicit square factor from a square.
--
-- If `a^2 * x = m^2` with `a` and `x` nonzero, every prime exponent of `m^2` is
-- even, the exponent contributed by `a^2` is even, and hence the exponent
-- contributed by `x` is even.  The accepted bridge
-- `OddPerfectNumber.Kernel.isSq_iff_even_factorization`
-- (theorem 28b00e2d-2e78-4683-8075-7135bec4a50b) then produces the witness.
--
-- This avoids the awkward `Nat` division that explicit root extraction would
-- otherwise need.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_isSq_iff_even_factorization

namespace OddPerfectNumber.Kernel
namespace Cancel

theorem isSq_of_sq_mul_eq_sq {a x m : Nat} (ha : a ≠ 0) (hx : x ≠ 0)
    (h : a ^ 2 * x = m ^ 2) : ∃ y, y ^ 2 = x := by
  have hax0 : a ^ 2 * x ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha) hx
  have hm0 : m ≠ 0 := by
    intro hm
    have hz : m ^ 2 = 0 := by rw [hm, Nat.zero_pow_of_pos (n := 2) (by norm_num)]
    rw [h, hz] at hax0
    exact hax0 rfl
  have hm2pos : 0 < m ^ 2 := pow_pos (Nat.pos_of_ne_zero hm0) _
  -- Every prime exponent of `m ^ 2` is even.
  have hm2even : ∀ p : Nat, Even ((m ^ 2).factorization p) :=
    (isSq_iff_even_factorization (Nat.ne_of_gt hm2pos)).mp ⟨m, rfl⟩
  -- Rewrite the hypothesis as an equality of factorizations.
  have hfac : (a ^ 2 * x).factorization = (m ^ 2).factorization := by
    rw [h]
  rw [Nat.factorization_mul (pow_ne_zero 2 ha) hx] at hfac
  rw [Nat.factorization_pow, Nat.factorization_pow] at hfac
  -- So for each `p`, `2 * a.factorization p + x.factorization p` is even.
  have hsum : ∀ p : Nat, Even (2 * a.factorization p + x.factorization p) := by
    intro p
    -- `hfac` is a `Finsupp` equation, so specialise it by application.  Keep the
    -- coefficient as `2 * _`: `Nat.two_mul` would rewrite it to `_ + _` on one
    -- side only and the two sides would no longer match.
    have this := congrArg (fun f : ℕ →₀ ℕ => f p) hfac
    simp only [Finsupp.nsmul_apply, Finsupp.add_apply, Nat.nsmul_eq_mul] at this
    have hmh := congrArg (fun f : ℕ →₀ ℕ => f p)
      (Nat.factorization_pow (m : ℕ) (k := 2))
    simp only [Finsupp.nsmul_apply, Nat.nsmul_eq_mul] at hmh
    -- Rewrite at this `p`, not inside the `∀`-bound `hm2even`.
    have heven : Even (2 * m.factorization p) := by rw [← hmh]; exact hm2even p
    -- `this` reads `2 * a.factorization p + x.factorization p = 2 * m.factorization p`.
    rw [this]; exact heven
  refine (isSq_iff_even_factorization hx).mpr ?_
  intro p
  -- `hsum p` says `2 * c + xf` is even, where `c = a.factorization p`.  Use
  -- `Nat.even_iff`, `Even n ↔ n % 2 = 0`, on the hypothesis, and close the
  -- goal with `Nat.even_add_one`/`omega` arithmetic modulo two: the term
  -- `2 * c` is `0 % 2`, leaving `xf % 2 = 0`.
  have heven : (2 * a.factorization p + x.factorization p) % 2 = 0 :=
    (Nat.even_iff).mp (hsum p)
  have hmod : (2 * a.factorization p) % 2 = 0 := by omega
  rw [Nat.add_mod, hmod] at heven
  exact (Nat.even_iff).mpr (by omega)

end Cancel
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {a x m : Nat} (ha : a ≠ 0) (hx : x ≠ 0)
    (h : a ^ 2 * x = m ^ 2) : ∃ y, y ^ 2 = x :=
  OddPerfectNumber.Kernel.Cancel.isSq_of_sq_mul_eq_sq ha hx h
