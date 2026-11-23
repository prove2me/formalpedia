-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kur_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:24.999117+00:00
-- url     : https://prove2.me/submissions/346ee07a-29da-4c6c-9727-b8628dea32ef

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kur_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_not_dvd_qK_pow_sub_one


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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) :
    MaximalUnramifiedExtension p K = K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ m : ℕ, ¬ p ∣ m ∧ ζ ^ m = 1} := by
  apply le_antisymm
  · refine iSup_le fun n => UnramifiedExtensions.Kn_le K le_sup_left fun ζ hζ => ?_
    exact (le_sup_right : _ ≤ K ⊔ _) (IntermediateField.subset_adjoin _ _
      ⟨_, UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK (Nat.succ_pos n), hζ⟩)
  · refine sup_le le_Kur (IntermediateField.adjoin_le_iff.2 ?_)
    rintro ζ ⟨m, hm, hζ⟩
    exact mem_Kur_of_pow hK hm hζ
end ReciprocityTheory.DiscreteGroups.LocalClassField
