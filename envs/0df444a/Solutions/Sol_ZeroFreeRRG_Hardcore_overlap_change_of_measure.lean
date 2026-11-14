-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_change_of_measure
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:36:24.455192+00:00
-- url     : https://prove2.me/submissions/5403c111-6146-4e9b-885e-95e852c09eaf

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution {Ω : Type} [Fintype Ω] (p q : Ω → ℝ) (D H Good : Ω → Prop)
    (L A B C : ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hL : 0 ≤ L)
    (hdens : ∀ x, H x → Good x → p x ≤ L * q x)
    (hmiss : (∑ x, if D x ∧ ¬ H x then p x else 0) ≤ A)
    (hreference : (∑ x, if H x then q x else 0) ≤ B)
    (htail : (∑ x, if ¬ Good x then p x else 0) ≤ C) :
    (∑ x, if D x then p x else 0) ≤ A + L * B + C := by
  classical
  have hpoint (x : Ω) : (if D x then p x else 0) ≤
      (if D x ∧ ¬ H x then p x else 0) + L * (if H x then q x else 0) +
        (if ¬ Good x then p x else 0) := by
    by_cases hD : D x <;> by_cases hH : H x <;> by_cases hG : Good x <;>
      simp only [hD,hH,hG,not_true_eq_false,not_false_eq_true, true_and, false_and,
        and_false, and_true, ↓reduceIte] <;>
      first | (have hh := hdens x hH hG; nlinarith [hp x, mul_nonneg hL (hq x)])
            | nlinarith [hp x, mul_nonneg hL (hq x)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  nlinarith [mul_le_mul_of_nonneg_left hreference hL]
