-- Prove2me | solution 1 for VectorCalculus.energy_conservation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:09:41.850961+00:00
-- url     : https://prove2.me/submissions/f3e1077b-87ca-4283-bd78-5a2ae71352b4

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
theorem solution {n : ℕ} (m : ℝ) (V : (Fin n → ℝ) → ℝ) (hV : ContDiff ℝ 1 V)
    (x : ℝ → (Fin n → ℝ)) (hx : ContDiff ℝ 2 x)
    (hnewton : ∀ (t : ℝ) (i : Fin n),
      m * deriv (fun s => deriv (fun u => x u i) s) t = -grad V (x t) i) :
    ∃ E : ℝ, ∀ t : ℝ,
      (1 / 2) * m * (∑ i, (deriv (fun s => x s i) t) ^ 2) + V (x t) = E := by
  have hVd : Differentiable ℝ V := hV.differentiable one_ne_zero
  have hxd : Differentiable ℝ x := hx.differentiable (by norm_num)
  -- each velocity coordinate is differentiable
  have hvd : ∀ i, Differentiable ℝ (fun s => deriv (fun u => x u i) s) := by
    intro i
    have hxi : ContDiff ℝ 2 (fun u => x u i) := (contDiff_apply ℝ ℝ i).comp hx
    exact (hxi.iterate_deriv' 1 1).differentiable one_ne_zero
  set E : ℝ → ℝ := fun t => (1 / 2) * m * (∑ i, (deriv (fun s => x s i) t) ^ 2) + V (x t)
  have hE : ∀ t, HasDerivAt E 0 t := by
    intro t
    have hk : HasDerivAt (fun t => (1 / 2) * m * (∑ i, (deriv (fun s => x s i) t) ^ 2))
        ((1 / 2) * m * ∑ i, 2 * deriv (fun s => x s i) t *
          deriv (fun s => deriv (fun u => x u i) s) t) t := by
      apply HasDerivAt.const_mul
      apply HasDerivAt.fun_sum
      intro i _
      have := ((hvd i) t).hasDerivAt.pow 2
      refine this.congr_deriv ?_
      first | ring | (norm_num; ring) | norm_num
    have hp := hasDerivAt_comp V hVd x hxd t
    refine (hk.add hp).congr_deriv ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have hn := hnewton t i
    linear_combination (deriv (fun s => x s i) t) * hn
  exact ⟨E 0, fun t => is_const_of_deriv_eq_zero (fun s => (hE s).differentiableAt)
    (fun s => (hE s).deriv) t 0⟩
