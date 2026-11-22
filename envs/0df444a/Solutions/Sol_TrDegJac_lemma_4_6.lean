-- Prove2me | solution 1 for TrDegJac.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T04:00:16.680526+00:00
-- url     : https://prove2.me/submissions/7cf2d488-daed-4905-977b-aa24dd6a791c

import Mathlib

set_option autoImplicit false

theorem solution {F : Type*} [Field F] {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) F)
    (g : MvPolynomial (Fin m) F) (i : Fin n) :
    MvPolynomial.pderiv i (MvPolynomial.aeval f g) =
      ∑ j, MvPolynomial.pderiv i (f j) * MvPolynomial.aeval f (MvPolynomial.pderiv j g) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a =>
      simp [MvPolynomial.pderiv_C]
  | add p q hp hq =>
      simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
      have hterm : ∀ j' : Fin m,
          MvPolynomial.aeval f (MvPolynomial.pderiv j' (p * MvPolynomial.X j))
            = MvPolynomial.aeval f (MvPolynomial.pderiv j' p) * f j
              + (if j' = j then MvPolynomial.aeval f p else 0) := by
        intro j'
        by_cases h : j' = j
        · subst h
          simp [MvPolynomial.pderiv_mul, MvPolynomial.aeval_X] <;> ring
        · simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne (Ne.symm h),
            MvPolynomial.aeval_X, h] <;> ring
      have hL : MvPolynomial.pderiv i (MvPolynomial.aeval f (p * MvPolynomial.X j))
          = MvPolynomial.pderiv i (MvPolynomial.aeval f p) * f j
            + MvPolynomial.aeval f p * MvPolynomial.pderiv i (f j) := by
        simp [MvPolynomial.pderiv_mul, MvPolynomial.aeval_X] <;> ring
      rw [hL, hp]
      have hR : (∑ j', MvPolynomial.pderiv i (f j')
            * MvPolynomial.aeval f (MvPolynomial.pderiv j' (p * MvPolynomial.X j)))
          = ∑ j', MvPolynomial.pderiv i (f j')
              * (MvPolynomial.aeval f (MvPolynomial.pderiv j' p) * f j
                + (if j' = j then MvPolynomial.aeval f p else 0)) :=
        Finset.sum_congr rfl (fun j' _ => by rw [hterm j'])
      rw [hR]
      simp only [mul_add, Finset.sum_add_distrib]
      have hsplit : ∀ j' : Fin m,
          MvPolynomial.pderiv i (f j') * (MvPolynomial.aeval f (MvPolynomial.pderiv j' p) * f j)
            = (MvPolynomial.pderiv i (f j')
                * MvPolynomial.aeval f (MvPolynomial.pderiv j' p)) * f j :=
        fun j' => by ring
      rw [Finset.sum_congr rfl (fun j' _ => hsplit j'), ← Finset.sum_mul]
      have h2 : ∀ j' : Fin m,
          MvPolynomial.pderiv i (f j') * (if j' = j then MvPolynomial.aeval f p else 0)
            = (if j' = j then MvPolynomial.pderiv i (f j') * MvPolynomial.aeval f p
                else 0) := by
        intro j'
        by_cases h : j' = j <;> simp [h]
      rw [Finset.sum_congr rfl (fun j' _ => h2 j')]
      have hsingle : (∑ j' : Fin m,
            if j' = j then MvPolynomial.pderiv i (f j') * MvPolynomial.aeval f p else 0)
          = MvPolynomial.pderiv i (f j) * MvPolynomial.aeval f p := by
        rw [Finset.sum_eq_single j] <;> simp_all
      rw [hsingle]
      ring
