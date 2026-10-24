-- Prove2me | solution 1 for SurelyBetter.CLB.theorem2_max_rep
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:08:24.096749+00:00
-- url     : https://prove2.me/submissions/2ca40671-b36a-466c-84cf-eb9766bfca26

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

open SurelyBetter.CLB

theorem solution {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) (hρ : 1 ≤ ρ E + ρ Eᶜ) :
    ∀ a ∈ U, ∀ b ∈ U, ∀ a' ∈ U, ∀ b' ∈ U,
      (V (binProf E a b) ≤ V (binProf E a' b') ↔
        max (ρ E * a + (1 - ρ E) * b) ((1 - ρ Eᶜ) * a + ρ Eᶜ * b) ≤
          max (ρ E * a' + (1 - ρ E) * b') ((1 - ρ Eᶜ) * a' + ρ Eᶜ * b')) := by
  clear hU hU2
  have hordered (a b : ℝ) (ha : a ∈ U) (hb : b ∈ U) :
      ∃ (F : Set S) (c d : ℝ), c ∈ U ∧ d ∈ U ∧ d ≤ c ∧
        binProf E a b = binProf F c d ∧
        max (ρ E * a + (1 - ρ E) * b) ((1 - ρ Eᶜ) * a + ρ Eᶜ * b) =
          W7 ρ F c d := by
    rcases le_total b a with hab | hab
    · refine ⟨E, a, b, ha, hb, hab, rfl, ?_⟩
      have hle : (1 - ρ Eᶜ) * a + ρ Eᶜ * b ≤ ρ E * a + (1 - ρ E) * b := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (sub_nonneg.mpr hab)]
      rw [max_eq_left hle]
      simp only [W7, mul_comm]
    · refine ⟨Eᶜ, b, a, hb, ha, hab, ?_, ?_⟩
      · funext s
        by_cases hs : s ∈ E <;> simp [binProf, hs]
      · have hle : ρ E * a + (1 - ρ E) * b ≤ (1 - ρ Eᶜ) * a + ρ Eᶜ * b := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hρ) (sub_nonneg.mpr hab)]
        rw [max_eq_right hle]
        simp only [W7, mul_comm, add_comm]
  intro a ha b hb a' ha' b' hb'
  obtain ⟨F, c, d, hc, hd, hdc, hprof, hmax⟩ := hordered a b ha hb
  obtain ⟨F', c', d', hc', hd', hdc', hprof', hmax'⟩ := hordered a' b' ha' hb'
  rw [hprof, hprof', hmax, hmax']
  exact hV.rep7 F F' c hc d hd c' hc' d' hd' hdc hdc'
