-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.orderOf_frobLK_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:01:08.563629+00:00
-- url     : https://prove2.me/submissions/4e2a78a1-2a49-4500-9913-e8d984449198

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_frobLK_Kn_pow_eq_one_iff

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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    orderOf (frobLK p K (Kn p K n)) = n := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((frobLK_Kn_pow_eq_one_iff hK hn n).2 dvd_rfl)
  · exact (frobLK_Kn_pow_eq_one_iff hK hn _).1 (pow_orderOf_eq_one _)
end ReciprocityTheory.DiscreteGroups.LocalClassField
