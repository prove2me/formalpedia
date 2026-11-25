-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylK_dual_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:35.523974+00:00
-- url     : https://prove2.me/submissions/cbdf4d7c-ed10-4d3b-9e1a-314e7d0a4d57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_eq_zero_of_down
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_viol_of_not_kDom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (s : Fin n) (h : ¬ KDom ε (Λ + dualWt n s)) : weylK ε (Λ + dualWt n s) = 0 := by
  obtain ⟨a, b, hab, hε, hlt⟩ := exists_viol_of_not_kDom ε _ h
  have hμ : ∀ c, (Λ + dualWt n s) c = Λ c - if c = s then 1 else 0 := by
    intro c
    simp only [Pi.add_apply, dualWt, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> ring
  by_cases has : ε a = ε s
  · exact weylK_eq_zero_of_down ε Λ _ s hint hdom (fun c _ => hμ c) hab hε has hlt
  · exfalso
    have ha : a ≠ s := fun h => has (h ▸ rfl)
    have hb : b ≠ s := fun h => has (h ▸ hε)
    rw [hμ, hμ, if_neg ha, if_neg hb] at hlt
    linarith [hdom a b hab hε]
end ReciprocityTheory.ChartRestriction.DS.HW
