-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CardG.card_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:39.147797+00:00
-- url     : https://prove2.me/submissions/ccad157b-8b81-4deb-b54d-d1d3095d96d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CardG_card_line
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open ReciprocityTheory.ChartRestriction.L1.CardG
namespace ReciprocityTheory.ChartRestriction.L1.CardG
theorem _root_.solution {F : Type} [Field F] [Fintype F] (a b c d : F) (hdet : a * d - b * c = 0)
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    (Finset.univ.filter (fun w : F × F => a * w.1 + b * w.2 = 0 ∧ c * w.1 + d * w.2 = 0)).card
      = Fintype.card F := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · rw [← card_line a b hab]
    congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun e => e.1, fun e => ⟨e, ?_⟩⟩
    rcases hab with h | h
    · apply mul_left_cancel₀ h
      linear_combination c * e + y * hdet
    · apply mul_left_cancel₀ h
      linear_combination d * e - x * hdet
  · push Not at hab
    obtain ⟨ha, hb⟩ := hab
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra hcd
      push Not at hcd
      exact hne ⟨ha, hb, hcd.1, hcd.2⟩
    rw [← card_line c d hcd]
    congr 1
    ext ⟨x, y⟩
    simp [ha, hb]
end ReciprocityTheory.ChartRestriction.L1.CardG
