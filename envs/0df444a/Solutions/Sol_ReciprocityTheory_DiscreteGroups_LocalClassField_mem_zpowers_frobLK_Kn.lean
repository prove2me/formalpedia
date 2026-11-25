-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_zpowers_frobLK_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:41.891017+00:00
-- url     : https://prove2.me/submissions/b86ff545-dec1-42e4-bac9-9c1319219a2b

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
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_exists_pow


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n)
    (g : GalLK p K (Kn p K n)) : g ∈ Subgroup.zpowers (frobLK p K (Kn p K n)) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨i, -, hi⟩ := IsFrobOn.exists_pow p K hK hn ((isFrob_frobK hK).isFrobOn n) σ
  refine ⟨i, ?_⟩
  change frobLK p K (Kn p K n) ^ (i : ℤ) = _
  rw [zpow_natCast, frobLK_pow]
  exact ((mk_eq_mk_iff _ _).2 hi).symm
end ReciprocityTheory.DiscreteGroups.LocalClassField
