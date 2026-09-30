-- Prove2me | solution 1 for StochQuasiNewton.SQN.suboptimality_le_gradient_sq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:07:35.545381+00:00
-- url     : https://prove2.me/submissions/81ffc04b-8a5c-4a8e-b0f8-aca26c5c13f5

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped RealInnerProductSpace
set_option autoImplicit false

private theorem quadratic_lower {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (lam : ℝ)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      lam * ‖v‖ ^ 2 < ⟪fderiv ℝ (gradient F) w v, v⟫)
    (w v : EuclideanSpace ℝ (Fin n)) :
    F w + ⟪gradient F w, v-w⟫ + lam / 2 * ‖v-w‖^2 ≤ F v := by
  let d := v-w
  let q : ℝ → ℝ := fun t => F (w+t • d) - lam/2*t^2*‖d‖^2
  let q' : ℝ → ℝ := fun t => ⟪gradient F (w+t • d), d⟫ - lam*t*‖d‖^2
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdG : Differentiable ℝ (gradient F) := by
    have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
      (hfder.differentiable (by norm_num))
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w+s • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add w
  have hq : ∀ t, HasDerivAt q (q' t) t := by
    intro t
    have hchain := (hdF (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [← inner_gradient_left] at hchain
    convert! hchain.sub (((hasDerivAt_id t).pow 2).const_mul (lam/2) |>.mul_const (‖d‖^2)) using 1 <;>
      dsimp only [q, q', id_eq] <;> ring
  have hq' : ∀ t, HasDerivAt q'
      (⟪fderiv ℝ (gradient F) (w+t • d) d, d⟫-lam*‖d‖^2) t := by
    intro t
    have hchain := (hdG (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    convert! (hchain.inner ℝ (hasDerivAt_const t d)).sub
      (((hasDerivAt_id t).const_mul lam).mul_const (‖d‖^2)) using 1 <;> simp [q']
  have hmono : Monotone q' := monotone_of_hasDerivAt_nonneg hq' (by
    intro t
    by_cases hd : d = 0
    · simp [hd]
    · exact sub_nonneg.mpr (hHess (w+t • d) d hd).le)
  have hconv : ConvexOn ℝ Set.univ q :=
    (show Monotone (deriv q) from fun x y hxy => by
      rw [(hq x).deriv, (hq y).deriv]; exact hmono hxy).monotoneOn (interior Set.univ) |>.convexOn_of_deriv
      convex_univ (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).differentiableAt.differentiableWithinAt)
  have hh := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0:ℝ)<1) (hq 0)
  simp [q, q', slope_def_field, d] at hh
  rw [inner_gradient_left, map_sub]
  linarith

theorem solution {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (lam : ℝ) (hlam : 0 < lam)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      lam * ‖v‖ ^ 2 < ⟪fderiv ℝ (gradient F) w v, v⟫)
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn F Set.univ wstar) :
    (∀ w v : EuclideanSpace ℝ (Fin n), F w - 1 / (2 * lam) * ‖gradient F w‖ ^ 2 ≤ F v) ∧
      ∀ w : EuclideanSpace ℝ (Fin n), 2 * lam * (F w - F wstar) ≤ ‖gradient F w‖ ^ 2 := by
  have hall : ∀ w v : EuclideanSpace ℝ (Fin n),
      F w - 1 / (2 * lam) * ‖gradient F w‖ ^ 2 ≤ F v := by
    intro w v
    have hq := quadratic_lower F hF lam hHess w v
    have hs := sq_nonneg ‖gradient F w + lam • (v-w)‖
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs] at hs
    have hcomp : -(1 / (2 * lam) * ‖gradient F w‖ ^ 2) ≤
        ⟪gradient F w, v-w⟫ + lam/2*‖v-w‖^2 := by
      apply (mul_le_mul_iff_right₀ (show 0 < 2*lam by positivity)).mp
      field_simp
      nlinarith
    linarith
  refine ⟨hall, fun w => ?_⟩
  have hh := mul_le_mul_of_nonneg_left (hall w wstar) (show 0 ≤ 2*lam by positivity)
  field_simp at hh
  nlinarith
