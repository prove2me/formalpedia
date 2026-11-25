-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.normGroup_self_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:16:02.076115+00:00
-- url     : https://prove2.me/submissions/098650f3-f061-4950-9b2f-15193c362047

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_pow_degree_mem_normGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution : normGrp p K K = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : degLK p K K = 1 := by
    have h2 : subG p K K = ⊤ := eq_top_iff.2 fun σ _ x hx => σ.commutes ⟨x, hx⟩
    show (subG p K K).index = 1
    rw [h2, Subgroup.index_top]
  have h3 := pow_degree_mem_normGroup (le_refl K) x
  rwa [h1, pow_one] at h3
end ReciprocityTheory.DiscreteGroups.LocalClassField
