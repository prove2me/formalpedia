-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:04.557815+00:00
-- url     : https://prove2.me/submissions/17558346-cdf7-4f76-a45b-71f855cfcadd

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kur_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_teichmuller_bar
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eqOn_Kur
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_sub_eq_one_of_pow_eq_one


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) (σ : GK p K) :
    σ ∈ subG p K (MaximalUnramifiedExtension p K) ↔ ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  constructor
  · intro h x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact lt_of_le_of_lt (UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [norm_GK]; exact hlt) hlt)
    · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := exists_teichmuller_bar x heq
      have h1 : σ ζ = ζ := h ζ (mem_Kur_of_pow hK hm hζ)
      have h2 : σ x - x = σ (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
      rw [h2]
      exact lt_of_le_of_lt (UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [norm_GK]; exact hxζ) hxζ)
  · intro h x hx
    refine eqOn_Kur (σ := σ) (τ := 1) (fun ζ m hm hζ => ?_) hK hx
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
    by_contra hne
    have h1 : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have h3 := norm_sub_eq_one_of_pow_eq_one p hm h1 hζ hne
    exact absurd h3 (ne_of_lt (h ζ (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le))
end ReciprocityTheory.DiscreteGroups.LocalClassField
