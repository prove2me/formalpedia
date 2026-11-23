-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_dvd_qK_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:25.966956+00:00
-- url     : https://prove2.me/submissions/8d2e7440-bc66-496b-b86a-d7fa993de079

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_eq_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_eq_pow


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : ¬ p ∣ m) :
    ∃ n, 0 < n ∧ m ∣ qK p K ^ n - 1 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))
  obtain ⟨f, hf, hq⟩ := qK_eq_pow p K hK
  have hcop : Nat.Coprime (qK p K) m := by
    rw [hq]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  refine ⟨Nat.totient m, Nat.totient_pos.2 hm0, ?_⟩
  have h1 : 1 ≤ qK p K ^ Nat.totient m := Nat.one_le_pow _ _ (by have := one_lt_qK p K hK; omega)
  exact (Nat.modEq_iff_dvd' h1).1 (Nat.ModEq.pow_totient hcop).symm
end ReciprocityTheory.DiscreteGroups.LocalClassField
