-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.frobLK_Kn_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:35:20.097659+00:00
-- url     : https://prove2.me/submissions/8f5b29b8-c6fc-4ab2-91b0-58b2416fabfb

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrob_frobK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrob_isFrobOn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_frobLK_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_mk_eq_mk_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_pow_fixes_iff


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    frobLK p K (Kn p K n) ^ i = 1 ↔ n ∣ i := by
  rw [frobLK_pow, ← IsFrobOn.pow_fixes_iff p K hK hn ((isFrob_frobK hK).isFrobOn n) i,
    ← QuotientGroup.mk_one, mk_eq_mk_iff]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
