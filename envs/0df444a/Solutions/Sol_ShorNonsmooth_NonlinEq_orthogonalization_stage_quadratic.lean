-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.orthogonalization_stage_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T14:06:36.072452+00:00
-- url     : https://prove2.me/submissions/2b1a3fab-683d-48d6-8193-76f1d1b70e54

import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_linear_bound_and_growth
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_endpoint_residual_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ ε > 0, ∃ c > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      ‖x 0‖ ≤ ε → ‖x n‖ ≤ c * ‖x 0‖ ^ 2 := by
  classical
  obtain ⟨ε₁, hε₁, c₁, hc₁, c₂, hc₂, hstage⟩ :=
    stage_linear_bound_and_growth ψ hψ h0 δ L hδ hLip hind
  obtain ⟨ε₂, hε₂, C, hC, hend⟩ :=
    stage_endpoint_residual_quadratic ψ hψ h0 δ L hδ hLip hind
  let ε : ℝ := min ε₁ ε₂
  let c : ℝ := C / c₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hc : 0 < c := div_pos hC hc₂
  refine ⟨ε, hε, c, hc, ?_⟩
  intro x hx hx0
  have hx₁ : ‖x 0‖ ≤ ε₁ := le_trans hx0 (min_le_left ε₁ ε₂)
  have hx₂ : ‖x 0‖ ≤ ε₂ := le_trans hx0 (min_le_right ε₁ ε₂)
  have hlower : c₂ * ‖x n‖ ≤ maxResidual ψ (x n) :=
    (hstage x hx hx₁).2
  have hupper : maxResidual ψ (x n) ≤ C * ‖x 0‖ ^ 2 :=
    hend x hx hx₂
  have hmul : c₂ * ‖x n‖ ≤ C * ‖x 0‖ ^ 2 :=
    le_trans hlower hupper
  calc
    ‖x n‖ = (1 / c₂) * (c₂ * ‖x n‖) := by field_simp [hc₂.ne']
    _ ≤ (1 / c₂) * (C * ‖x 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = c * ‖x 0‖ ^ 2 := by
      dsimp [c]
      ring
