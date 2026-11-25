-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_Kn_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:50:21.060958+00:00
-- url     : https://prove2.me/submissions/13b4b2ac-21a8-46eb-8a40-b43c6c6caf63

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_le_Kn_of_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_degLK_pos
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eq_Kn_of_norm
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_subG_eq_of_isOpen
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finrank_eq_degLK_mul
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_le_iff


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) (U : Subgroup (GK p K))
    (hU : IsOpen (U : Set (GK p K))) (h : subG p K (MaximalUnramifiedExtension p K) ≤ U) :
    ∃ n, 0 < n ∧ U = subG p K (Kn p K n) := by
  obtain ⟨M, hKM, hM, rfl⟩ := exists_subG_eq_of_isOpen hK U hU
  have hMur : M ≤ MaximalUnramifiedExtension p K := by
    have := (subG_le_iff hKM).1 h
    rwa [sup_eq_right.2 le_Kur] at this
  obtain ⟨N, hN, hMN⟩ := exists_le_Kn_of_le_Kur hK hM hMur
  refine ⟨degLK p K M, degLK_pos hM, ?_⟩
  rw [← eq_Kn_of_norm p K hK hKM (degLK_pos hM) (finrank_eq_degLK_mul hKM hM)
    (fun x hx => norm_Kn p K hK hN (hMN hx))]
end ReciprocityTheory.DiscreteGroups.LocalClassField
