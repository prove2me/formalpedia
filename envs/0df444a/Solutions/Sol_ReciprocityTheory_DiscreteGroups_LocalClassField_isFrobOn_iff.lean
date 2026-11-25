-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isFrobOn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:44:37.666936+00:00
-- url     : https://prove2.me/submissions/af234f43-0220-4aa6-8f20-0e0e75181a38

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_pow_sub_one_ne_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_teichmuller
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_not_dvd_qK_pow_sub_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_sigBar_red
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_teichmuller
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finiteDimensional_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_qK_Kn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (φ : GK p K) :
    IsFrobOn p K n φ ↔ ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → φ ζ = ζ ^ qK p K := by
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  constructor
  · intro h ζ hζ
    by_contra hne
    have h1 := UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ
    have h2 := h ζ (mem_Kn_of_pow p K hζ) h1.le
    have h3 := norm_sub_eq_one_of_pow_eq_one p (UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn)
      (ζ := φ ζ) (ξ := ζ ^ qK p K) (by rw [← map_pow, hζ, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]) hne
    rw [h3] at h2
    exact lt_irrefl _ h2
  · intro h x hx hx1
    have hex : ∃ ζ : PadicAlgCl p, φ ζ = ζ ^ qK p K ∧ ‖ζ‖ ≤ 1 ∧ ‖x - ζ‖ < 1 := by
      rcases lt_or_eq_of_le hx1 with h1 | h1
      · exact ⟨0, by rw [map_zero, zero_pow (by omega)], by simp, by simpa using h1⟩
      · obtain ⟨ζ, -, hζ, hxζ⟩ := exists_teichmuller p (Kn p K n) (finiteDimensional_Kn p K hK hn) hx h1
        rw [qK_Kn p K hK hn] at hζ
        exact ⟨ζ, h ζ hζ, (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le, hxζ⟩
    obtain ⟨ζ, h1, h2, h3⟩ := hex
    have h4 : UnramifiedExtensions.red x = UnramifiedExtensions.red ζ := (UnramifiedExtensions.red_eq_iff hx1 h2).2 h3
    have h5 : ‖φ x‖ ≤ 1 := by rw [norm_GK]; exact hx1
    have h6 : ‖x ^ qK p K‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx1
    rw [← UnramifiedExtensions.red_eq_iff h5 h6, ← UnramifiedExtensions.sigBar_red φ hx1, h4, UnramifiedExtensions.sigBar_red φ h2, h1,
      UnramifiedExtensions.red_pow h2, UnramifiedExtensions.red_pow hx1, h4]
end ReciprocityTheory.DiscreteGroups.LocalClassField
