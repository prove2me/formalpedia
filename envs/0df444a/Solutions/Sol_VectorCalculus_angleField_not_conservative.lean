-- Prove2me | solution 1 for VectorCalculus.angleField_not_conservative
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:22:58.170521+00:00
-- url     : https://prove2.me/submissions/3494094e-ac84-40e4-88b9-6f554987e58a

import Mathlib
import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_grad
import Definitions.Def_VectorCalculus_conservative
import Definitions.Def_VectorCalculus_angleField

open VectorCalculus

namespace NCAux
/-- Along a line where the field component is nonzero, the potential has that component as an
honest derivative. -/
lemma edge {φ : (Fin 2 → ℝ) → ℝ} (hφ : ∀ y, angleField y = grad φ y) (i : Fin 2)
    (p : ℝ → (Fin 2 → ℝ)) (hp : ∀ s x, Function.update (p x) i s = p s)
    (hpi : ∀ x, p x i = x) (g : ℝ → ℝ) (hg : ∀ x, angleField (p x) i = g x)
    (hg0 : ∀ x, g x ≠ 0) (x : ℝ) :
    HasDerivAt (fun s => φ (p s)) (g x) x := by
  have hpd : partialDeriv φ i (p x) = g x := by rw [← hg, hφ]; rfl
  unfold partialDeriv at hpd
  have hfun : (fun s : ℝ => φ (Function.update (p x) i s)) = fun s => φ (p s) := by
    funext s; rw [hp]
  rw [hfun, hpi] at hpd
  have hdiff : DifferentiableAt ℝ (fun s => φ (p s)) x := by
    by_contra hnd
    rw [deriv_zero_of_not_differentiableAt hnd] at hpd
    exact hg0 x hpd.symm
  rw [← hpd]
  exact hdiff.hasDerivAt

lemma int_eq (a : ℝ) : ∫ x in (-1 : ℝ)..1, a / (x ^ 2 + 1) = a * (Real.pi / 2) := by
  have : (fun x : ℝ => a / (x ^ 2 + 1)) = fun x => a * (1 / (1 + x ^ 2)) := by
    funext x; rw [add_comm]; ring
  rw [this, intervalIntegral.integral_const_mul, integral_one_div_one_add_sq, Real.arctan_one,
    Real.arctan_neg, Real.arctan_one]
  ring

lemma ftc {φ : (Fin 2 → ℝ) → ℝ} (hφ : ∀ y, angleField y = grad φ y) (i : Fin 2)
    (p : ℝ → (Fin 2 → ℝ)) (hp : ∀ s x, Function.update (p x) i s = p s)
    (hpi : ∀ x, p x i = x) (a : ℝ) (ha : a ≠ 0) (hg : ∀ x, angleField (p x) i = a / (x ^ 2 + 1)) :
    φ (p 1) - φ (p (-1)) = a * (Real.pi / 2) := by
  have hg0 : ∀ x : ℝ, a / (x ^ 2 + 1) ≠ 0 := fun x => div_ne_zero ha (by positivity)
  rw [← int_eq a]
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => edge hφ i p hp hpi (fun x => a / (x ^ 2 + 1)) hg hg0 x)
  exact (Continuous.div continuous_const (by fun_prop) (fun x => by positivity)).intervalIntegrable _ _

end NCAux
open NCAux

theorem solution : ¬ IsConservative angleField := by
  rintro ⟨φ, -, hφ⟩
  -- bottom edge y = -1: component 0 is 1/(x²+1)
  have hb := ftc hφ 0 (fun x => ![x, -1]) (fun s x => by ext j; fin_cases j <;> simp)
    (fun x => by simp) 1 one_ne_zero (fun x => by simp [angleField])
  -- top edge y = 1: component 0 is -1/(x²+1)
  have ht := ftc hφ 0 (fun x => ![x, 1]) (fun s x => by ext j; fin_cases j <;> simp)
    (fun x => by simp) (-1) (by norm_num) (fun x => by first | (simp [angleField]; done) | (simp [angleField]; ring))
  -- right edge x = 1: component 1 is 1/(1+y²)
  have hr := ftc hφ 1 (fun y => ![1, y]) (fun s y => by ext j; fin_cases j <;> simp)
    (fun y => by simp) 1 one_ne_zero (fun y => by first | (simp [angleField]; done) | (simp [angleField]; ring))
  -- left edge x = -1: component 1 is -1/(1+y²)
  have hl := ftc hφ 1 (fun y => ![-1, y]) (fun s y => by ext j; fin_cases j <;> simp)
    (fun y => by simp) (-1) (by norm_num) (fun y => by first | (simp [angleField]; done) | (simp [angleField]; ring))
  have hπ := Real.pi_pos
  linarith
