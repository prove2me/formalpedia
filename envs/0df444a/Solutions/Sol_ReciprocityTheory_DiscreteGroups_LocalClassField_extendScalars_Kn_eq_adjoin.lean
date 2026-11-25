-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.extendScalars_Kn_eq_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:23.170845+00:00
-- url     : https://prove2.me/submissions/f70d4e41-fb19-45a5-9103-6f0e5cea032f

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kn_of_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (qK p K ^ n - 1))
    (hm : qK p K ^ n - 1 ≠ 0) :
    IntermediateField.extendScalars (le_Kn p K n) = IntermediateField.adjoin K {ζ} := by
  apply le_antisymm
  · have h : Kn p K n ≤ (IntermediateField.adjoin K {ζ}).restrictScalars ℚ_[p] := by
      apply UnramifiedExtensions.Kn_le
      · intro y hy
        exact (IntermediateField.adjoin K {ζ}).algebraMap_mem ⟨y, hy⟩
      · intro ξ hξ
        have : NeZero (qK p K ^ n - 1) := ⟨hm⟩
        obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
        exact pow_mem (IntermediateField.mem_adjoin_simple_self K ζ) i
    exact h
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact mem_Kn_of_pow p K hζ.pow_eq_one
end ReciprocityTheory.DiscreteGroups.LocalClassField
