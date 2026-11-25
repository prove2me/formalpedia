-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.exists_consec_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:27.892016+00:00
-- url     : https://prove2.me/submissions/073db183-0aa2-452c-8fd2-c451f88abef1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish

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
theorem _root_.solution (ε : Fin n → Bool) {s b : Fin n} (hsb : s < b) (hε : ε s = ε b) :
    ∃ b', s < b' ∧ b' ≤ b ∧ ε s = ε b' ∧ ∀ c, s < c → c < b' → ε c ≠ ε s := by
  set S := univ.filter fun c => s < c ∧ ε c = ε s with hS
  have hne : S.Nonempty := ⟨b, by simp [hS, hsb, hε]⟩
  have hm := S.min'_mem hne
  simp only [hS, mem_filter, mem_univ, true_and] at hm
  refine ⟨S.min' hne, hm.1, S.min'_le b (by simp [hS, hsb, hε]), hm.2.symm, fun c h1 h2 he => ?_⟩
  have : c ∈ S := by simp [hS, h1, he]
  exact absurd (S.min'_le c this) (not_le.2 h2)
end ReciprocityTheory.ChartRestriction.DS.HW
