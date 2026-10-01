-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_cyclotomic_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T21:08:21.41698+00:00
-- url     : https://prove2.me/submissions/f54c9fc3-2c82-43aa-bf62-076d516932cb

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.five_two_prime_cyclotomic_split
--          81a70179-c0e7-41e8-97bd-86af2cb90f91
--
-- The contextual parity allocation for the `omega = 2` residual, specialised to
-- the `k = 5` blocks `U = p ^ 2 + p + 1` and `V = ((p + 1) / 2) * (p ^ 2 - p + 1)`.
--
-- The first Dris equation `2 * m ^ 2 = (2 * U * V) * (d1 ^ 2 * (q * r))`
-- rearranges, without any division, to `d1 ^ 2 * (q * r * U * V) = m ^ 2`, which
-- is exactly the shape of the accepted `isSq_of_sq_mul_eq_sq` (74779081); so
-- `q * r * U * V` is a square.  Coprimality of the blocks is the accepted
-- `five_cyclotomic_block_coprime` (2c9214f0), `U` is not a square by the
-- accepted `five_cyclotomic_factors_ne_square` (648a7dc4), and the product block
-- `V` is not a square by the accepted hp4 child
-- `five_second_cyclotomic_product_not_square` (62a8c541).  The counting child
-- `two_prime_block_is_prime_mul_sq` (672c3afb) then makes `U = t * x ^ 2` with
-- `t` one of `q, r`, which is the required split.
--
-- Diagnostic notes for this revision (all from candidate 5146, remote
-- 7caadddc, which returned CE):
--   * line 79 `Nat.mul_right_cancel 2 h2` is wrong; the goal is
--     `2 * m ^ 2 = 2 * X`, which needs a *left* cancellation, so the proof uses
--     `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by norm_num)) h2`.
--     The earlier unknown `Nat.mul_right_cancel` left an unassigned `?m.997`
--     metavariable in every later application, so all of the `line 91`..`line 100`
--     mismatches were cascade rather than independent faults.
--   * revision 2 (candidate 5153, remote 92ca0ef9, CE) fixed that cancellation
--     but left three further faults, all in the `0 < m` step:
--     the `0 < 2` proof must be passed as a `0 < ?n` hypothesis, not as the
--     argument of `Nat.pos_of_ne_zero`, since that lemma takes it implicitly;
--     `Nat.eq_zero_of_pos_iff` does not exist in this revision; and
--     `Nat.pow_ne_zero` does not exist either.
--   * revision 3 therefore writes the positivity proof explicitly as
--     `(show (0 : Nat) < 2 from by omega)` and replaces every use of
--     `Nat.pow_ne_zero` with `Nat.eq_of_mul_eq_mul_left (show (0 : Nat) < 2 from
--     by omega)`.  This is the idiom already used by the accepted mission proof
--     `mme_recursive_x_hash_finite_usable_isolation` (8e5aadc6), which writes
--     `(Nat.eq_of_mul_eq_mul_left hV heq).le`.
--   * revision 4 fixes the two faults reported by candidate 5161 (remote
--     2a079139, CE).  First, `Nat.eq_of_mul_eq_mul_left` is
--     `{m k n : Nat} (hn : 0 < n) (h : n * m = n * k) : m = k`, so applied to
--     `h2 : 2 * m ^ 2 = 2 * X` it returns `m ^ 2 = X`, whereas `hshape` needs
--     `X = m ^ 2`; revision 3 used a bare `exact`, which failed with a type
--     mismatch against the reversed expectation.  It now takes `.symm`.
--     Second, `isSq_of_sq_mul_eq_sq` returns `y ^ 2 = q * r * (U * V)` because
--     `hshape` parenthesises the blocks, whereas `two_prime_block_is_prime_mul_sq`
--     expects `y ^ 2 = q * r * a * b` with `a = U` and `b = V`, i.e. the
--     right-associated `q * r * U * V`.  Revision 4 passes the reassociated
--     existential.  Candidate `90b_...C` is the same mathematics written with an
--     explicit `symm` and a witness-level `rw [hy, mul_assoc]`, to separate the
--     two repair idioms in case one of them is what the elaborator wants.
--   * every `!= 0` binder is a Bool coercion, so each helper is first proved in
--     `Prop` form (`≠`) and only then handed to the published Bool-shaped child.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_block_coprime
import Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_factors_ne_square
import Theorems.Thm_OddPerfectNumber_Kernel_five_second_cyclotomic_product_not_square
import Theorems.Thm_OddPerfectNumber_Kernel_isSq_of_sq_mul_eq_sq
import Theorems.Thm_OddPerfectNumber_Kernel_two_prime_block_is_prime_mul_sq

namespace OddPerfectNumber.Kernel
namespace SplitB

private theorem bool_of_ne {n : Nat} (h : n ≠ 0) : n != 0 := by simpa using h

theorem solution_aux (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime)
    (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    (∃ x, p ^ 2 + p + 1 = q * x ^ 2) ∨ (∃ x, p ^ 2 + p + 1 = r * x ^ 2) := by
  classical
  have hp2' : p ≠ 2 := by simpa using hp2
  have hqr' : q ≠ r := Nat.ne_of_lt hqr
  have hp2ge : 2 ≤ p := hp.two_le
  have hp2gt : 2 < p := by omega
  -- The two blocks are nonzero, coprime, and both non-squares.
  have hUnz : (p ^ 2 + p + 1 : Nat) ≠ 0 := by omega
  have hVnz : ((p + 1) / 2 * (p ^ 2 - p + 1) : Nat) ≠ 0 := by
    refine mul_ne_zero ?_ (Nat.ne_of_gt (by omega))
    rcases hp.odd_of_ne_two hp2' with ⟨k, hk⟩
    rw [show (p + 1) / 2 = k + 1 by omega]
    omega
  have hUV : Nat.gcd (p ^ 2 + p + 1) ((p + 1) / 2 * (p ^ 2 - p + 1)) = 1 :=
    five_cyclotomic_block_coprime p hp2
  obtain ⟨hUnsq, _⟩ := five_cyclotomic_factors_ne_square p hp2gt
  have hVnsq : ¬ ∃ y, y ^ 2 = ((p + 1) / 2 * (p ^ 2 - p + 1) : Nat) := by
    rintro ⟨y, hy⟩
    exact five_second_cyclotomic_product_not_square p hp hp4 ⟨y, hy.symm⟩
  -- The first Dris equation gives `d1 ^ 2 * (q * r * U * V) = m ^ 2`.
  have hshape : (d1 ^ 2 * (q * r * ((p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) : Nat)))
      = m ^ 2 := by
    have h2 : 2 * m ^ 2
        = 2 * (d1 ^ 2 * (q * r * ((p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) : Nat))) := by
      calc 2 * m ^ 2
          = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)) := h1
        _ = 2 * (d1 ^ 2 * (q * r * ((p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1)) : Nat))) := by
          ring
    exact (Nat.eq_of_mul_eq_mul_left (show (0 : Nat) < 2 from by omega) h2).symm
  have hprod0 : q * r * ((p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1) : Nat)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hq.ne_zero hr.ne_zero) (mul_ne_zero hUnz hVnz)
  -- `d1 ^ 2` is a factor of `m ^ 2`, and every other factor is nonzero, so `d1`
  -- itself is nonzero: otherwise `hshape` would read `0 = m ^ 2`.
  have hd10 : d1 ≠ 0 := by
    rintro hd
    have hmz : m ^ 2 = 0 := by
      rw [← hshape]
      simp [hd]
    have hm0 : m = 0 := eq_zero_of_pow_eq_zero hmz
    rw [hm0] at hm
    exact absurd hm (by simp)
  obtain ⟨y, hy⟩ := isSq_of_sq_mul_eq_sq hd10 hprod0 hshape
  -- Feed the square relation to the counting child.  `isSq_of_sq_mul_eq_sq`
  -- returns `y ^ 2 = q * r * (U * V)`; the counting child wants the
  -- right-associated `q * r * U * V`, which is exactly `mul_assoc`.
  have hsq' : ∃ y, y ^ 2 = q * r * (p ^ 2 + p + 1) *
      ((p + 1) / 2 * (p ^ 2 - p + 1) : Nat) := by
    refine ⟨y, ?_⟩
    have hq2 : y ^ 2 = q * r * (p ^ 2 + p + 1) *
        ((p + 1) / 2 * (p ^ 2 - p + 1) : Nat) := by
      rw [hy]
      ring
    exact hq2
  obtain ⟨t, x, ht, hUx, hin⟩ :=
    two_prime_block_is_prime_mul_sq (bool_of_ne hUnz) (bool_of_ne hVnz) hUV hq hr
      (by simpa [hqr']) hsq' hUnsq hVnsq
  rcases hin with htin | htin
  · refine Or.inl ⟨x, ?_⟩
    rw [hUx, htin]
  · refine Or.inr ⟨x, ?_⟩
    rw [hUx, htin]

end SplitB
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime)
    (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    (∃ x, p ^ 2 + p + 1 = q * x ^ 2) ∨ (∃ x, p ^ 2 + p + 1 = r * x ^ 2) :=
  OddPerfectNumber.Kernel.SplitB.solution_aux p m d1 q r hp hp2 hp4 hm hpm hq hr hqr h1
