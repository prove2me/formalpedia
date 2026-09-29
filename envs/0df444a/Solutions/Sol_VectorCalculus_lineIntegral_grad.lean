-- Prove2me | solution 1 for VectorCalculus.lineIntegral_grad
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:09:41.985288+00:00
-- url     : https://prove2.me/submissions/1313eaab-fe25-4202-9a8d-a34139353dc7

import Mathlib
import Definitions.Def_VectorCalculus_lineIntegral
import Definitions.Def_VectorCalculus_grad

open VectorCalculus

namespace VCAux

lemma partialDeriv_eq {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : Differentiable ℝ φ) (y : Fin n → ℝ)
    (i : Fin n) : partialDeriv φ i y = fderiv ℝ φ y (Pi.single i 1) := by
  unfold partialDeriv
  have hf := hasDerivAt_update y i (y i)
  have hl : HasFDerivAt φ (fderiv ℝ φ y) (Function.update y i (y i)) := by
    rw [Function.update_eq_self]; exact (hφ y).hasFDerivAt
  exact (hl.comp_hasDerivAt (y i) hf).deriv

lemma coord_deriv {n : ℕ} (x : ℝ → (Fin n → ℝ)) (hx : Differentiable ℝ x) (t : ℝ) (i : Fin n) :
    deriv (fun s => x s i) t = deriv x t i :=
  ((hasDerivAt_pi.mp (hx t).hasDerivAt) i).deriv

lemma fderiv_sum {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin n → ℝ) = v i • Pi.single i (1 : ℝ) := by
    ext j; by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- `d/dt φ(x t) = Σᵢ ∂ᵢφ(x t) · xᵢ'(t)`. -/
lemma hasDerivAt_comp {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : Differentiable ℝ φ)
    (x : ℝ → (Fin n → ℝ)) (hx : Differentiable ℝ x) (t : ℝ) :
    HasDerivAt (fun t => φ (x t)) (∑ i, grad φ (x t) i * deriv (fun s => x s i) t) t := by
  have h1 := (hφ (x t)).hasFDerivAt.comp_hasDerivAt t (hx t).hasDerivAt
  have e : fderiv ℝ φ (x t) (deriv x t) = ∑ i, grad φ (x t) i * deriv (fun s => x s i) t := by
    rw [fderiv_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [grad, partialDeriv_eq φ hφ, coord_deriv x hx]
  rw [← e]
  exact h1

end VCAux

open VCAux
theorem solution {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (x : ℝ → (Fin n → ℝ)) (hx : ContDiff ℝ 1 x) (a b : ℝ) :
    lineIntegral (grad φ) x a b = φ (x b) - φ (x a) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hxd : Differentiable ℝ x := hx.differentiable one_ne_zero
  unfold lineIntegral
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_comp φ hφd x hxd t)
  apply Continuous.intervalIntegrable
  have hcont : Continuous fun t => fderiv ℝ φ (x t) (deriv x t) :=
    ((hφ.continuous_fderiv (by norm_num)).comp hx.continuous).clm_apply (hx.continuous_deriv (by norm_num))
  have e : (fun t => ∑ i, grad φ (x t) i * deriv (fun s => x s i) t) =
      fun t => fderiv ℝ φ (x t) (deriv x t) := by
    funext t
    rw [fderiv_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [grad, partialDeriv_eq φ hφd, coord_deriv x hxd]
  rw [e]
  exact hcont
