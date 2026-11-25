-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:35:28.28181+00:00
-- url     : https://prove2.me/submissions/ffbec877-b5f7-4ee0-93d8-0c16cb9e72dd

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finiteDimensional_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_eq_degLK_mul
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : degLK p K (Kn p K n) = n := by
  have h1 := finrank_eq_degLK_mul (le_Kn p K n) (finiteDimensional_Kn p K hK hn)
  rw [finrank_Kn p K hK hn] at h1
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_right hd h1).symm
end ReciprocityTheory.DiscreteGroups.LocalClassField
