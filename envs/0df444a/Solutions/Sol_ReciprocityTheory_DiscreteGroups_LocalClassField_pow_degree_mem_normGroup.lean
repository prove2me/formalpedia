-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.pow_degree_mem_normGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:55.537368+00:00
-- url     : https://prove2.me/submissions/1a2e90e6-4819-4737-80a3-8210f0f26d65

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_of_mem_base
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_normGrp_iff


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
theorem _root_.solution (h : K ≤ L) (x : Kˣ) : x ^ degLK p K L ∈ normGrp p K L := by
  rw [mem_normGrp_iff]
  refine ⟨ofK p K (Additive.ofMul x), h (ofK_mem p K _), ?_⟩
  rw [normHom_of_mem_base _ (ofK_mem p K _), ofMul_pow, map_nsmul]
end ReciprocityTheory.DiscreteGroups.LocalClassField
