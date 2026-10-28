-- Prove2me | solution 1 for PDASNewton.FunSpace.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:27:00.026066+00:00
-- url     : https://prove2.me/submissions/8b4a36a2-ac99-4c90-921a-56313e6f5f8b

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting
import Definitions.Def_PDASNewton_FunSpace_Setting

open Filter Topology

theorem solution {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (F : X → Z) (G : X → X →L[ℝ] Z) (U : Set X) (xstar : X)
    (hU : IsOpen U) (hxU : xstar ∈ U) (hF : F xstar = 0)
    (hslant : PDASNewton.Local.IsSlantingFunction F G U)
    (hinv : ∃ M : ℝ, ∀ x ∈ U, ∃ Ginv : Z →L[ℝ] X,
      Ginv.comp (G x) = ContinuousLinearMap.id ℝ X ∧
      (G x).comp Ginv = ContinuousLinearMap.id ℝ Z ∧ ‖Ginv‖ ≤ M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℕ → X, ‖x 0 - xstar‖ < ρ →
      (∀ k, G (x k) (x (k + 1) - x k) = -F (x k)) →
      PDASNewton.Local.ConvergesSuperlinearly x xstar := by
  obtain ⟨M, hM⟩ := hinv
  have hrem : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : X, ‖h‖ < δ →
      ‖F (xstar + h) - F xstar - G (xstar + h) h‖ ≤ ε * ‖h‖ := by
    intro ε hε
    have := (hslant xstar hxU).def hε
    rcases Metric.eventually_nhds_iff.1 this with ⟨δ, hδ, hball⟩
    exact ⟨δ, hδ, fun h hh => hball (by simpa [dist_eq_norm] using hh)⟩
  obtain ⟨δU, hδU, hballU⟩ := Metric.isOpen_iff.1 hU xstar hxU
  have step : ∀ (x : ℕ → X), (∀ k, G (x k) (x (k + 1) - x k) = -F (x k)) → ∀ k, x k ∈ U →
      ‖x (k + 1) - xstar‖ ≤
        M * ‖F (xstar + (x k - xstar)) - F xstar - G (xstar + (x k - xstar)) (x k - xstar)‖ := by
    intro x hN k hk
    obtain ⟨Ginv, hl, _, hGn⟩ := hM (x k) hk
    have e1 : xstar + (x k - xstar) = x k := by abel
    rw [e1, hF, sub_zero]
    have e2 : x (k + 1) - xstar = Ginv (G (x k) (x (k + 1) - xstar)) := by
      have := congrArg (fun L => L (x (k + 1) - xstar)) hl
      simpa using this.symm
    have e3 : G (x k) (x (k + 1) - xstar) = -(F (x k) - G (x k) (x k - xstar)) := by
      have : x (k + 1) - xstar = (x (k + 1) - x k) + (x k - xstar) := by abel
      rw [this, map_add, hN k]; abel
    rw [e2, e3, map_neg, norm_neg]
    calc ‖Ginv (F (x k) - G (x k) (x k - xstar))‖
        ≤ ‖Ginv‖ * ‖F (x k) - G (x k) (x k - xstar)‖ := Ginv.le_opNorm _
      _ ≤ M * ‖F (x k) - G (x k) (x k - xstar)‖ := mul_le_mul_of_nonneg_right hGn (norm_nonneg _)
  have hM0 : 0 ≤ M := by
    obtain ⟨Ginv, _, _, hGn⟩ := hM xstar hxU
    exact (norm_nonneg _).trans hGn
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = max M 1 := ⟨_, rfl⟩
  have hMM' : M ≤ M' := hM' ▸ le_max_left _ _
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (hM' ▸ le_max_right _ _)
  obtain ⟨δ1, hδ1, hr1⟩ := hrem (1 / (2 * M')) (by positivity)
  refine ⟨min δ1 δU, lt_min hδ1 hδU, ?_⟩
  intro x hx0 hN
  have hinU : ∀ k, ‖x k - xstar‖ < min δ1 δU → x k ∈ U := by
    intro k hk
    apply hballU
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hk (min_le_right _ _)
  have hcontr : ∀ k, ‖x k - xstar‖ < min δ1 δU →
      ‖x (k + 1) - xstar‖ ≤ 1 / 2 * ‖x k - xstar‖ := by
    intro k hk
    have h1 := step x hN k (hinU k hk)
    have h2 := hr1 (x k - xstar) (lt_of_lt_of_le hk (min_le_left _ _))
    have hMc : M * (1 / (2 * M')) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
    calc ‖x (k + 1) - xstar‖ ≤ M * (1 / (2 * M') * ‖x k - xstar‖) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hM0)
      _ = (M * (1 / (2 * M'))) * ‖x k - xstar‖ := by ring
      _ ≤ 1 / 2 * ‖x k - xstar‖ := mul_le_mul_of_nonneg_right hMc (norm_nonneg _)
  have hgeo : ∀ k, ‖x k - xstar‖ < min δ1 δU ∧ ‖x k - xstar‖ ≤ (1 / 2) ^ k * ‖x 0 - xstar‖ := by
    intro k
    induction k with
    | zero => exact ⟨hx0, by simp⟩
    | succ k ih =>
      have h := hcontr k ih.1
      have hn := norm_nonneg (x k - xstar)
      refine ⟨lt_of_le_of_lt h (by linarith [ih.1]), ?_⟩
      calc ‖x (k + 1) - xstar‖ ≤ 1 / 2 * ‖x k - xstar‖ := h
        _ ≤ 1 / 2 * ((1 / 2) ^ k * ‖x 0 - xstar‖) := by linarith [ih.2]
        _ = (1 / 2) ^ (k + 1) * ‖x 0 - xstar‖ := by ring
  have htend : Tendsto x atTop (𝓝 xstar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun k => norm_nonneg _) (fun k => (hgeo k).2)
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const ‖x 0 - xstar‖
    simpa using this
  refine ⟨htend, ?_⟩
  intro η hη
  obtain ⟨δ2, hδ2, hr2⟩ := hrem (η / M') (by positivity)
  have hev : ∀ᶠ k in atTop, ‖x k - xstar‖ < δ2 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 htend).eventually (gt_mem_nhds hδ2)
  filter_upwards [hev] with k hk
  have h1 := step x hN k (hinU k (hgeo k).1)
  have h2 := hr2 _ hk
  have hMc : M * (η / M') ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ hM'pos]; nlinarith
  calc ‖x (k + 1) - xstar‖ ≤ M * (η / M' * ‖x k - xstar‖) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hM0)
    _ = (M * (η / M')) * ‖x k - xstar‖ := by ring
    _ ≤ η * ‖x k - xstar‖ := mul_le_mul_of_nonneg_right hMc (norm_nonneg _)
