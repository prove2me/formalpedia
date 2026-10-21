-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.homogeneous_diagonal_linearization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:07:34.447324+00:00
-- url     : https://prove2.me/submissions/0b6ac6b6-2834-4564-8125-b2e2398f15e9

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

open QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

theorem g66b_lin_const {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]
    (k : ℕ) : ∀ (q : A → B) (x v : A),
    linearization q x k (fun _ => v) = (fwdDiff v)^[k] q x := by
  induction k with
  | zero => intro q x v; rfl
  | succ k ih =>
    intro q x v
    show linearization (fun y => q (y + v) - q y) x k (fun _ => v) = _
    rw [ih, Function.iterate_succ_apply]
    rfl

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

theorem solution
    (q : E → F) (k : ℕ) (hq : IsScalarHomogeneous (K := K) k q) :
    ∀ x : E, linearization q 0 k (fun _ => x) = (Nat.factorial k) • q x := by
  intro x
  rw [g66b_lin_const, fwdDiff_iter_eq_sum_shift]
  have key := congr_fun (fwdDiff_iter_eq_factorial (R := K) (n := k)) 0
  rw [fwdDiff_iter_eq_sum_shift] at key
  have h1 : ∀ j ∈ Finset.range (k + 1),
      ((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) • q (0 + j • x) =
        (((-1 : ℤ) ^ (k - j) * (k.choose j : ℤ)) • (0 + j • (1 : K)) ^ k) • q x := by
    intro j _
    rw [zero_add, zero_add, ← Nat.cast_smul_eq_nsmul K j x, hq, smul_assoc,
      nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_smul, key]
  simp [Nat.cast_smul_eq_nsmul]
