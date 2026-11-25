-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isFrob_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:50.069845+00:00
-- url     : https://prove2.me/submissions/288577ce-ac95-4a2a-9926-3dcfda5935d0

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_teichmuller_bar
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_of_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_sigBar_red
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_qK


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
    IsFrob p K σ ↔ ∀ (ζ : PadicAlgCl p) (m : ℕ), ¬ p ∣ m → ζ ^ m = 1 → σ ζ = ζ ^ qK p K := by
  constructor
  · intro h ζ m hm hζ
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
    by_contra hne
    have h1 : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
    have h2 : (ζ ^ qK p K) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    have h3 := norm_sub_eq_one_of_pow_eq_one p hm h1 h2 hne
    exact absurd h3 (ne_of_lt (h ζ (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le))
  · intro h x hx
    have hq : qK p K ≠ 0 := by have := one_lt_qK p K hK; omega
    have hσx : ‖σ x‖ ≤ 1 := by rw [norm_GK]; exact hx
    have hxq : ‖x ^ qK p K‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    rw [← UnramifiedExtensions.red_eq_iff hσx hxq, ← UnramifiedExtensions.sigBar_red σ hx, UnramifiedExtensions.red_pow hx]
    rcases lt_or_eq_of_le hx with hlt | heq
    · have h0 : UnramifiedExtensions.red x = 0 := by
        rw [UnramifiedExtensions.red_of_le hx, UnramifiedExtensions.res_eq_zero_iff]; exact hlt
      rw [h0, map_zero, zero_pow hq]
    · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := exists_teichmuller_bar x heq
      have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
      have hζ1 := (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le
      rw [(UnramifiedExtensions.red_eq_iff hx hζ1).2 hxζ, UnramifiedExtensions.sigBar_red σ hζ1, h ζ m hm hζ, UnramifiedExtensions.red_pow hζ1]
end ReciprocityTheory.DiscreteGroups.LocalClassField
