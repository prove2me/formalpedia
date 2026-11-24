-- Prove2me | solution 1 for Poly1305.poly1305_eq_add16_H
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:05:01.641371+00:00
-- url     : https://prove2.me/submissions/a83a68ce-61c1-459e-9f8a-df3053542c53

import Definitions.Def_Poly1305Bernstein
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Fin

section
section
namespace Poly1305.DefsAdd

theorem sum_digits (n k : ℕ) :
    ∑ j ∈ Finset.range k, 2 ^ (8 * j) * (n / 2 ^ (8 * j) % 256) = n % 2 ^ (8 * k) := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 8 * (k + 1) = 8 * k + 8 by ring, pow_add,
      Nat.mod_mul]
    norm_num

theorem leVal_toStr16 (n : ℕ) : leVal (toStr16 n) = n % 2 ^ 128 := by
  unfold leVal toStr16
  simp only
  rw [Fin.sum_univ_eq_sum_range (fun j => 2 ^ (8 * j) * (n / 2 ^ (8 * j) % 256)) 16]
  exact sum_digits n 16

theorem eval_poly (r : ℕ) (m : Message) :
    (poly m).eval (r : ℤ) =
      ((∑ i ∈ Finset.Icc 1 (numChunks m), chunk m i * r ^ (numChunks m + 1 - i) : ℕ) : ℤ) := by
  unfold poly
  simp [Polynomial.eval_finsetSum]

end Poly1305.DefsAdd

namespace Poly1305

theorem poly1305_eq_add16_H_dev (r : ℕ) (m : Message) (s : Str16) :
    poly1305 r m s = add16 (H r m) s := by
  unfold poly1305 add16 H
  rw [DefsAdd.leVal_toStr16, DefsAdd.eval_poly]
  generalize (∑ i ∈ Finset.Icc 1 (numChunks m), chunk m i * r ^ (numChunks m + 1 - i)) = x
  have : (((x : ℤ) % (p1305 : ℤ)).toNat) = x % p1305 := by
    rw [← Int.natCast_mod, Int.toNat_natCast]
  rw [this]
  generalize x % p1305 = y
  generalize (2 : ℕ) ^ 128 = M
  rw [Nat.mod_mod, Nat.add_mod (y % M), Nat.mod_mod, ← Nat.add_mod]

end Poly1305

end
end

section
open Poly1305

theorem solution (r : ℕ) (m : Message) (s : Str16) :
    poly1305 r m s = add16 (H r m) s := by
  apply Poly1305.poly1305_eq_add16_H_dev <;> assumption

end
