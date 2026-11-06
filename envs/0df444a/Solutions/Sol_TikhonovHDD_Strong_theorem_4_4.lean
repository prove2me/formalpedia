-- Prove2me | solution 1 for TikhonovHDD.Strong.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:09:32.040658+00:00
-- url     : https://prove2.me/submissions/f92b4f96-a5d0-41b0-bf11-65586b78f93d

import Mathlib
import Definitions.Def_TikhonovHDD_Strong_Setting
import Theorems.Thm_TikhonovHDD_Strong_theorem_4_4_case_I
import Theorems.Thm_TikhonovHDD_Strong_theorem_4_4_case_II
import Theorems.Thm_TikhonovHDD_Strong_theorem_4_4_case_III

open Set Filter Topology
open TikhonovHDD.Strong

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) (xstar : H)
    (ht₀ : 0 < t₀) (hα : 3 ≤ α) (hβ : 0 ≤ β)
    (hGA : GeneralAssumption g t₀ ε ε')
    (hx : IsSolution g α β t₀ ε u₀ v₀ x xd xdd)
    (hε_int : MeasureTheory.IntegrableOn (fun t => ε t / t) (Ici t₀))
    (hε_lim : Tendsto
      (fun t => β / (ε t * t ^ (α / 3 + 1)) * ∫ s in t₀..t, ε s ^ 2 * s ^ (α / 3 + 1))
      atTop (𝓝 0))
    (hε_deriv : ∃ a > (1 : ℝ), ∃ t₁ ≥ t₀, ∀ t ≥ t₁, ε' t ≤ -(a * β / 2) * ε t ^ 2)
    (hα3 : α = 3 → Tendsto (fun t => t ^ 2 * ε t) atTop atTop)
    (hα3lt : 3 < α → ∃ c > (0 : ℝ),
      ∀ᶠ t in atTop, 2 / 3 * α * (1 / 3 * α - 1 + β * c ^ 2) ≤ t ^ 2 * ε t)
    (hxstar : IsMinNormMinimizer g xstar) :
    (∀ δ > (0 : ℝ), ∃ᶠ t in atTop, ‖x t - xstar‖ < δ) ∧
      ((∃ T ≥ t₀, (∀ t ≥ T, ‖x t‖ < ‖xstar‖) ∨ (∀ t ≥ T, ‖xstar‖ ≤ ‖x t‖)) →
        Tendsto (fun t => ‖x t - xstar‖) atTop (𝓝 0)) := by
  -- strong convergence in the two "trajectory ends on one side" cases
  have hconv : (∃ T ≥ t₀, (∀ t ≥ T, ‖x t‖ < ‖xstar‖) ∨ (∀ t ≥ T, ‖xstar‖ ≤ ‖x t‖)) →
      Tendsto (fun t => ‖x t - xstar‖) atTop (𝓝 0) := by
    rintro ⟨T, hT, hin | hout⟩
    · exact (tendsto_iff_norm_sub_tendsto_zero).1
        (theorem_4_4_case_II g α β t₀ ε ε' u₀ v₀ x xd xdd xstar ht₀ hα hβ hGA hx hε_int
          hε_lim hε_deriv hα3 hα3lt hxstar ⟨T, hT, hin⟩)
    · exact (tendsto_iff_norm_sub_tendsto_zero).1
        (theorem_4_4_case_I g α β t₀ ε ε' u₀ v₀ x xd xdd xstar ht₀ hα hβ hGA hx hε_int
          hε_lim hε_deriv hα3 hα3lt hxstar ⟨T, hT, hout⟩)
  refine ⟨?_, hconv⟩
  intro δ hδ
  by_cases hA : ∃ T ≥ t₀, (∀ t ≥ T, ‖x t‖ < ‖xstar‖) ∨ (∀ t ≥ T, ‖xstar‖ ≤ ‖x t‖)
  · have h := hconv hA
    exact ((h.eventually (gt_mem_nhds hδ))).frequently
  · push_neg at hA
    have hin : ∀ T ≥ t₀, ∃ t ≥ T, ‖x t‖ < ‖xstar‖ := fun T hT => (hA T hT).2
    have hout : ∀ T ≥ t₀, ∃ s ≥ T, ‖xstar‖ ≤ ‖x s‖ := fun T hT => by
      obtain ⟨s, hs, h⟩ := (hA T hT).1
      exact ⟨s, hs, h⟩
    exact theorem_4_4_case_III g α β t₀ ε ε' u₀ v₀ x xd xdd xstar ht₀ hα hβ hGA hx hε_int
      hε_lim hε_deriv hα3 hα3lt hxstar hin hout δ hδ
