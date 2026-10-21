-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.maxResidual_active_signed_inner_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T12:57:54.307627+00:00
-- url     : https://prove2.me/submissions/762ce9cd-771b-4cef-8d07-510997d03f45

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_local_inverse_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : ∀ i, ψ i xstar = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U)
    (hJ : (jacobianMatrix ψ xstar).det ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, ∀ i, |ψ i x| = maxResidual ψ x →
      |inner ℝ (gradient (ψ i) x) (x - xstar) - ψ i x| ≤
        δ * maxResidual ψ x := by
  classical
  obtain ⟨V₀, hV₀, C, hCpos, hbound⟩ :=
    maxResidual_local_inverse_bound ψ xstar hroot U hU hψ hJ
  let η : ℝ := δ / (2 * C)
  have hηpos : 0 < η := by positivity
  have hmax_nonneg : ∀ x, 0 ≤ maxResidual ψ x := by
    intro x
    unfold maxResidual
    exact Real.iSup_nonneg (fun i => abs_nonneg _)
  have hTaylor : ∀ i, ∀ᶠ x in nhds xstar,
      ‖ψ i x - fderiv ℝ (ψ i) xstar (x - xstar)‖ ≤ η * ‖x - xstar‖ := by
    intro i
    have hdiff : DifferentiableAt ℝ (ψ i) xstar :=
      ((hψ i).contDiffAt hU).differentiableAt_one
    convert hdiff.hasFDerivAt.isLittleO.def hηpos using 1
    ext x
    simp [hroot i]
  have hGrad : ∀ i, ∀ᶠ x in nhds xstar,
      ‖gradient (ψ i) x - gradient (ψ i) xstar‖ ≤ η := by
    intro i
    have hcont : ContinuousAt (fun y => gradient (ψ i) y) xstar := by
      have hf := ((hψ i).contDiffAt hU).continuousAt_fderiv one_ne_zero
      change ContinuousAt (fun y =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
          (fderiv ℝ (ψ i) y)) xstar
      exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.continuousAt.comp hf
    exact (hcont.eventually (Metric.ball_mem_nhds (gradient (ψ i) xstar) hηpos)).mono
      (fun x hx => le_of_lt hx)
  have hev : ∀ᶠ x in nhds xstar, ∀ i,
      ‖ψ i x - fderiv ℝ (ψ i) xstar (x - xstar)‖ ≤ η * ‖x - xstar‖ ∧
        ‖gradient (ψ i) x - gradient (ψ i) xstar‖ ≤ η :=
    Filter.eventually_all.mpr (fun i => (hTaylor i).and (hGrad i))
  rcases Filter.eventually_iff_exists_mem.mp hev with ⟨V₁, hV₁, hV₁bound⟩
  refine ⟨V₀ ∩ V₁, Filter.inter_mem hV₀ hV₁, ?_⟩
  intro x hx i hi
  rcases hx with ⟨hx₀, hx₁⟩
  let d := x - xstar
  have hxinv : ‖d‖ ≤ C * maxResidual ψ x := by
    simpa [d] using hbound x hx₀
  have hFnonneg : 0 ≤ maxResidual ψ x := hmax_nonneg x
  have hCη : C * η = δ / 2 := by
    simp [η, hCpos.ne']
    field_simp [hCpos.ne']
  have hbase : |inner ℝ (gradient (ψ i) xstar) d - ψ i x| ≤ η * ‖d‖ := by
    have ht := (hV₁bound x hx₁ i).1
    have hf : fderiv ℝ (ψ i) xstar d = inner ℝ (gradient (ψ i) xstar) d := by
      simp [d, gradient, InnerProductSpace.toDual_symm_apply]
    rw [hf] at ht
    simpa [Real.norm_eq_abs, abs_sub_comm] using ht
  have hgrad : |inner ℝ (gradient (ψ i) x) d - inner ℝ (gradient (ψ i) xstar) d| ≤ η * ‖d‖ := by
    have hg := (hV₁bound x hx₁ i).2
    calc
      |inner ℝ (gradient (ψ i) x) d - inner ℝ (gradient (ψ i) xstar) d|
          = |inner ℝ (gradient (ψ i) x - gradient (ψ i) xstar) d| := by
              rw [inner_sub_left]
      _ ≤ ‖gradient (ψ i) x - gradient (ψ i) xstar‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ η * ‖d‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
  have hdecomp : inner ℝ (gradient (ψ i) x) d - ψ i x =
      (inner ℝ (gradient (ψ i) x) d - inner ℝ (gradient (ψ i) xstar) d) +
        (inner ℝ (gradient (ψ i) xstar) d - ψ i x) := by ring
  have hηd : η * ‖d‖ ≤ δ / 2 * maxResidual ψ x := by
    calc
      η * ‖d‖ ≤ η * (C * maxResidual ψ x) := mul_le_mul_of_nonneg_left hxinv hηpos.le
      _ = δ / 2 * maxResidual ψ x := by rw [← hCη]; ring
  calc
    |inner ℝ (gradient (ψ i) x) (x - xstar) - ψ i x|
        = |inner ℝ (gradient (ψ i) x) d - ψ i x| := by rfl
    _ = |(inner ℝ (gradient (ψ i) x) d - inner ℝ (gradient (ψ i) xstar) d) +
          (inner ℝ (gradient (ψ i) xstar) d - ψ i x)| := by rw [hdecomp]
    _ ≤ |inner ℝ (gradient (ψ i) x) d - inner ℝ (gradient (ψ i) xstar) d| +
          |inner ℝ (gradient (ψ i) xstar) d - ψ i x| := abs_add_le _ _
    _ ≤ η * ‖d‖ + η * ‖d‖ := add_le_add hgrad hbase
    _ ≤ δ / 2 * maxResidual ψ x + δ / 2 * maxResidual ψ x := add_le_add hηd hηd
    _ = δ * maxResidual ψ x := by ring
