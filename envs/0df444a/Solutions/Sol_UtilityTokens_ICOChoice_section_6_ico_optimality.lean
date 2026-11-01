-- Prove2me | solution 1 for UtilityTokens.ICOChoice.section_6_ico_optimality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:48:00.019704+00:00
-- url     : https://prove2.me/submissions/bebf3d87-31c7-43e8-b500-148748bbda31

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting
import Theorems.Thm_UtilityTokens_ICOChoice_proposition_1
import Theorems.Thm_UtilityTokens_ICOChoice_proposition_2
import Theorems.Thm_UtilityTokens_ICOChoice_lemma_1
import Theorems.Thm_UtilityTokens_ICOChoice_ico_revenues_larger
import Theorems.Thm_UtilityTokens_ICOChoice_appendix_a_F_increasing

open UtilityTokens.ICOChoice

theorem solution (f : ℝ) (hf : 0 < f) :
    (∀ Θ x : ℝ, 1 < Θ → Θ ≤ UtilityTokens.ICOChoice.thetaTilde → 0 < x →
      UtilityTokens.ICOChoice.optPayoffI Θ x f < UtilityTokens.ICOChoice.optPayoffT Θ x) ∧
    (∀ Θ : ℝ, UtilityTokens.ICOChoice.thetaTilde < Θ → Θ ≤ 3 →
      0 < UtilityTokens.ICOChoice.xbar Θ f ∧
        ∀ x : ℝ, 0 < x → (UtilityTokens.ICOChoice.optPayoffT Θ x ≤
          UtilityTokens.ICOChoice.optPayoffI Θ x f ↔ UtilityTokens.ICOChoice.xbar Θ f ≤ x)) ∧
    StrictAntiOn (fun Θ => UtilityTokens.ICOChoice.xbar Θ f)
      (Set.Ioc UtilityTokens.ICOChoice.thetaTilde 3) := by
  obtain ⟨_, ⟨_, hT3⟩, hle, _, _⟩ := lemma_1
  refine ⟨?_, ?_, ?_⟩
  · intro Θ x h1 hΘ hx
    have hΘ0 : 0 < Θ := by linarith
    have hT := (proposition_1 Θ x h1 (by linarith) hx).2.2.2
    have hI := (proposition_2 Θ x f h1 hx).2.2.2.2.2
    rw [hT, hI]
    simp only [hle Θ h1 hΘ]
    have : (1 * ((Θ - 1) / Θ) ^ 2 + (1 - (Θ - 1) / Θ) * ((Θ - 1) / Θ)) * x
        = (Θ - 1) / Θ * x := by field_simp; ring
    linarith
  · intro Θ hΘ hΘ3
    have hF : 0 < Fden Θ := (ico_revenues_larger Θ 1 f hΘ hΘ3 one_pos).2.1
    refine ⟨div_pos hf hF, fun x hx => ?_⟩
    have heq := (ico_revenues_larger Θ x f hΘ hΘ3 hx).2.2
    unfold xbar
    rw [div_le_iff₀ hF]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · intro a ha b hb hab
    have hFa : 0 < Fden a := (ico_revenues_larger a 1 f ha.1 ha.2 one_pos).2.1
    have hlt : Fden a < Fden b := appendix_a_F_increasing.2 ha.1 hb.1 hab
    exact div_lt_div_of_pos_left hf hFa hlt
