-- Prove2me | solution 1 for TranscendenceTheory.quadratic_pair_power_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T20:46:03.130276+00:00
-- url     : https://prove2.me/submissions/8fa5a628-2be3-42e0-8a65-cca6af0910ac

import Mathlib.Algebra.QuadraticAlgebra.Basic

private lemma quadratic_pair_iterate
    (R : Type*) [CommRing R] (d a b : R) (n : ℕ) :
    let T : ℕ → R × R := Nat.rec (1, 0)
      (fun _ t => (a * t.1 + d * b * t.2, b * t.1 + a * t.2))
    let q : QuadraticAlgebra R d 0 := ⟨a, b⟩
    T n = ((q ^ n).re, (q ^ n).im) := by
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only
    rw [ih]
    simp only [pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    congr 1 <;> ring

theorem solution
    (R : Type*) [CommRing R] (d a b y : R) (hy : y ^ 2 = d) :
    let T : ℕ → R × R := Nat.rec (1, 0)
      (fun _ t => (a * t.1 + d * b * t.2, b * t.1 + a * t.2))
    ∀ n : ℕ,
      (a + y * b) ^ n = (T n).1 + y * (T n).2 ∧
        (T n).1 ^ 2 - d * (T n).2 ^ 2 = (a ^ 2 - d * b ^ 2) ^ n := by
  dsimp only
  intro n
  have hT := quadratic_pair_iterate R d a b n
  dsimp only at hT
  rw [hT]
  let q : QuadraticAlgebra R d 0 := ⟨a, b⟩
  have hroot : y * y = d • (1 : R) + (0 : R) • y := by
    simpa [pow_two] using hy
  let f : QuadraticAlgebra R d 0 →ₐ[R] R := QuadraticAlgebra.lift ⟨y, hroot⟩
  constructor
  · simpa [f, q, QuadraticAlgebra.lift_apply_apply, smul_eq_mul, mul_comm] using
      (map_pow f q n).symm
  · simpa [q, QuadraticAlgebra.norm_def, pow_two, mul_assoc] using
      (map_pow (QuadraticAlgebra.norm : QuadraticAlgebra R d 0 →* R) q n)
