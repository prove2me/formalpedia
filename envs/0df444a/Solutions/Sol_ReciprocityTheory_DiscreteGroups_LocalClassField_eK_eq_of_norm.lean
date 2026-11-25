-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.eK_eq_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:41:14.313774+00:00
-- url     : https://prove2.me/submissions/dbe160fa-bc3c-43cf-bb47-4c870ccdbdf4

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_valueGroup_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) (hn : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : eK p L = eK p K := by
  have h1 : valueGroup p L = valueGroup p K := by
    refine le_antisymm ?_ (valueGroup_mono p h)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hn _ hx
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [norm_zero, norm_eq_zero] at hxy
      exact (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero hxy
    refine ⟨Additive.ofMul (Units.mk0 y hy0), hy, ?_⟩
    rw [vbar_apply p x, hxy]
    rfl
  unfold eK
  rw [h1]
end ReciprocityTheory.DiscreteGroups.LocalClassField
