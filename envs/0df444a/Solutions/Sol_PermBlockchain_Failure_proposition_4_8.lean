-- Prove2me | solution 1 for PermBlockchain.Failure.proposition_4_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T16:16:48.282724+00:00
-- url     : https://prove2.me/submissions/e01535ea-c745-4c62-87f2-e733d37c8fd5

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_PermBlockchain_Failure_Setting

set_option autoImplicit false

namespace PermBlockchain.Failure.Aux9f
open MeasureTheory

lemma pt (a b φ : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b) - |φ| ≤ max a φ - max b φ := by
  rcases le_total φ b with h | h
  · rw [max_eq_left (h.trans hab), max_eq_left h]; linarith [abs_nonneg φ]
  · rcases le_total φ a with h' | h'
    · rw [max_eq_left h', max_eq_right h]; linarith [le_abs_self φ]
    · rw [max_eq_right h', max_eq_right h]; linarith [le_abs_self φ]

lemma wc_diff {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable id μ) (a b : ℝ)
    (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b) - ∫ φ, |φ| ∂μ ≤ (∫ φ, max a φ ∂μ) - ∫ φ, max b φ ∂μ := by
  have hA : Integrable (fun φ : ℝ => max a φ) μ := (integrable_const a).sup hi
  have hB : Integrable (fun φ : ℝ => max b φ) μ := (integrable_const b).sup hi
  have hAbs : Integrable (fun φ : ℝ => |φ|) μ := hi.abs
  rw [← integral_sub hA hB]
  have e : ∫ φ, ((a - b) - |φ|) ∂μ = (a - b) - ∫ φ, |φ| ∂μ := by
    rw [integral_sub (integrable_const _) hAbs, integral_const]; simp
  rw [← e]
  exact integral_mono ((integrable_const _).sub hAbs) (hA.sub hB) (fun φ => pt a b φ hb hab)

end PermBlockchain.Failure.Aux9f

open PermBlockchain.Failure in
theorem solution {m : ℕ} (M : Model m) (hM : M.Standing) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ < Δ → M.Assumption1 Δ → M.AdoptionFailure Δ := by
  have := hM.isProbabilityMeasure
  refine ⟨max (2 * (∫ φ, |φ| ∂M.μ) - 2 * ((M.WV .F 0 - M.WV .N 0) + (M.WM .F - M.WM .N))
      - (M.h - M.l)) (max (2 * M.γ - 2 * M.L - M.h - M.l) 0), fun Δ hΔ _ => ?_⟩
  have h1 := lt_of_le_of_lt (le_max_left _ _) hΔ
  have h23 := lt_of_le_of_lt (le_max_right _ _) hΔ
  have h2 := lt_of_le_of_lt (le_max_left _ _) h23
  have h3 := lt_of_le_of_lt (le_max_right _ _) h23
  constructor
  · have hWV : M.WV .F Δ - M.WV .N Δ = M.WV .F 0 - M.WV .N 0 := by
      simp only [Model.WV, Model.Ψh, Model.sl, Model.Ψl]; ring
    have hb : 0 ≤ M.u .N Δ := by simp only [Model.u]; linarith
    have hab : M.u .N Δ ≤ M.u .F Δ := by simp only [Model.u]; linarith [hM.l_lt_h]
    have hwc : (M.u .F Δ - M.u .N Δ) - ∫ φ, |φ| ∂M.μ ≤ M.WC .F Δ - M.WC .N Δ :=
      PermBlockchain.Failure.Aux9f.wc_diff hM.integrable_id (M.u .F Δ) (M.u .N Δ) hb hab
    have hu : M.u .F Δ - M.u .N Δ = (Δ + M.h - M.l) / 2 := by simp only [Model.u]; ring
    unfold Model.W
    linarith
  · intro hE
    unfold Model.IsEquilibrium AGT.IsPureNash at hE
    obtain ⟨i⟩ : Nonempty (Mfr m) := ⟨(0, true, ⟨0, by have := hM.two_le_m; omega⟩)⟩
    have := hE i false
    simp [Model.payoff, Model.grossProfit, Scenario.profile] at this
    linarith [hM.χ_pos i]
