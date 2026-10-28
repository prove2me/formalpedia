-- Prove2me | solution 1 for PDASNewton.Local.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:46:19.872827+00:00
-- url     : https://prove2.me/submissions/f8860890-78bc-48f7-afac-75a6f783725a

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting

open Filter Topology in
open PDASNewton.Local in
theorem solution {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (F : X → Z) (G : X → X →L[ℝ] Z) (U : Set X) (xstar : X)
    (hU : IsOpen U) (hxU : xstar ∈ U) (hF : F xstar = 0)
    (hG : IsSlantingFunction F G U)
    (hinv : ∃ M : ℝ, ∀ x ∈ U, ∃ Ginv : Z →L[ℝ] X,
      Ginv.comp (G x) = ContinuousLinearMap.id ℝ X ∧
      (G x).comp Ginv = ContinuousLinearMap.id ℝ Z ∧ ‖Ginv‖ ≤ M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℕ → X, ‖x 0 - xstar‖ < ρ →
      (∀ k, G (x k) (x (k + 1) - x k) = -F (x k)) → ConvergesSuperlinearly x xstar := by
  obtain ⟨M, hM⟩ := hinv
  have hM0 : 0 ≤ M := by
    obtain ⟨Gi, -, -, h⟩ := hM xstar hxU
    exact le_trans (norm_nonneg _) h
  -- residual
  let r : X → Z := fun h => F (xstar + h) - F xstar - G (xstar + h) h
  have hr : r =o[𝓝 0] (fun h => h) := hG xstar hxU
  have hsmall : ∀ c : ℝ, 0 < c → ∃ δ > 0, ∀ h : X, ‖h‖ < δ → ‖r h‖ ≤ c * ‖h‖ := by
    intro c hc
    have := hr.def hc
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp this
    refine ⟨δ, hδ, fun h hh => hball ?_⟩
    rwa [dist_zero_right]
  -- one Newton step
  have step : ∀ (y y' : X), y ∈ U → G y (y' - y) = -F y →
      ‖y' - xstar‖ ≤ M * ‖r (y - xstar)‖ := by
    intro y y' hy hstep
    obtain ⟨Gi, hGi1, -, hGi3⟩ := hM y hy
    have hy' : xstar + (y - xstar) = y := by abel
    have key : G y (y' - xstar) = -r (y - xstar) := by
      simp only [r, hy', hF, sub_zero]
      have : y' - xstar = (y' - y) + (y - xstar) := by abel
      rw [this, map_add, hstep]
      abel
    have : y' - xstar = -Gi (r (y - xstar)) := by
      have h1 : Gi (G y (y' - xstar)) = y' - xstar := by
        have := congrArg (fun T => T (y' - xstar)) hGi1
        simpa using this
      rw [← h1, key, map_neg]
    rw [this, norm_neg]
    exact le_trans (Gi.le_opNorm _) (mul_le_mul_of_nonneg_right hGi3 (norm_nonneg _))
  obtain ⟨δ1, hδ1, hball1⟩ := hsmall (1 / (2 * (M + 1))) (by positivity)
  obtain ⟨δ2, hδ2, hball2⟩ := Metric.isOpen_iff.mp hU xstar hxU
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun x hx0 hstep => ?_⟩
  have hρ1 : ‖x 0 - xstar‖ < δ1 := lt_of_lt_of_le hx0 (min_le_left _ _)
  have hρ2 : ‖x 0 - xstar‖ < δ2 := lt_of_lt_of_le hx0 (min_le_right _ _)
  have hcontr : ∀ k, ‖x k - xstar‖ ≤ ‖x 0 - xstar‖ * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : ‖x k - xstar‖ ≤ ‖x 0 - xstar‖ := by
        refine le_trans ih ?_
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
      have hkU : x k ∈ U := hball2 (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
      have h1 := step (x k) (x (k + 1)) hkU (hstep k)
      have h2 := hball1 (x k - xstar) (by linarith)
      have h3 : M * (1 / (2 * (M + 1))) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
      have h4 : ‖x (k + 1) - xstar‖ ≤ 1 / 2 * ‖x k - xstar‖ := by
        calc ‖x (k + 1) - xstar‖ ≤ M * ‖r (x k - xstar)‖ := h1
          _ ≤ M * (1 / (2 * (M + 1)) * ‖x k - xstar‖) := mul_le_mul_of_nonneg_left h2 hM0
          _ = (M * (1 / (2 * (M + 1)))) * ‖x k - xstar‖ := by ring
          _ ≤ 1 / 2 * ‖x k - xstar‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      calc ‖x (k + 1) - xstar‖ ≤ 1 / 2 * ‖x k - xstar‖ := h4
        _ ≤ 1 / 2 * (‖x 0 - xstar‖ * (1 / 2) ^ k) := by gcongr
        _ = ‖x 0 - xstar‖ * (1 / 2) ^ (k + 1) := by ring
  have hU' : ∀ k, x k ∈ U := by
    intro k
    apply hball2
    rw [Metric.mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (hcontr k) (lt_of_le_of_lt ?_ hρ2)
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  have htend : Tendsto x atTop (𝓝 xstar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun k : ℕ => ‖x 0 - xstar‖ * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul ‖x 0 - xstar‖
      simpa using this
    exact squeeze_zero (fun k => norm_nonneg _) hcontr hlim
  refine ⟨htend, fun η hη => ?_⟩
  obtain ⟨δ3, hδ3, hball3⟩ := hsmall (η / (M + 1)) (by positivity)
  have hev : ∀ᶠ k in atTop, ‖x k - xstar‖ < δ3 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp htend).eventually (gt_mem_nhds hδ3)
    exact this
  filter_upwards [hev] with k hk
  have h1 := step (x k) (x (k + 1)) (hU' k) (hstep k)
  have h2 := hball3 (x k - xstar) hk
  have h3 : M * (η / (M + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  calc ‖x (k + 1) - xstar‖ ≤ M * ‖r (x k - xstar)‖ := h1
    _ ≤ M * (η / (M + 1) * ‖x k - xstar‖) := mul_le_mul_of_nonneg_left h2 hM0
    _ = (M * (η / (M + 1))) * ‖x k - xstar‖ := by ring
    _ ≤ η * ‖x k - xstar‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
