-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.mem_of_pow_qK_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:25:35.899665+00:00
-- url     : https://prove2.me/submissions/ce4fffe9-9415-4efc-b97e-e2d0b45dc59f

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_coe
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_red_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_of_fixed
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_not_dvd_qK_pow_sub_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K - 1) = 1) : ζ ∈ K := by
  have hq := one_lt_qK K hK
  have hnd : ¬ p ∣ qK p K - 1 := by simpa using not_dvd_qK_pow_sub_one K hK (n := 1) one_pos
  have hm0 : qK p K - 1 ≠ 0 := by omega
  have h1 := norm_eq_one_of_pow hm0 hζ
  have hc : red ζ ∈ resK p K := by
    apply mem_resK_of_pow K hK
    rw [← red_pow h1.le]
    congr 1
    have : qK p K = (qK p K - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  obtain ⟨x, hx, hxc⟩ := (mem_resK_iff K _).1 hc
  rw [← red_coe, red_eq_iff (norm_le_one x) h1.le] at hxc
  apply mem_of_fixed K
  intro σ
  by_contra hne
  have hσζ : (σ ζ) ^ (qK p K - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have h2 := norm_sub_eq_one_of_pow_eq_one hnd hσζ hζ hne
  have hσx : σ (x : PadicAlgCl p) = x := σ.commutes ⟨x, hx⟩
  have h3 : σ ζ - ζ = ((x : PadicAlgCl p) - ζ) - σ ((x : PadicAlgCl p) - ζ) := by
    rw [map_sub, hσx]; ring
  have h4 : ‖σ ζ - ζ‖ < 1 := by
    rw [h3]
    refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt hxc ?_)
    rw [norm_GK]; exact hxc
  exact absurd h2 (ne_of_lt h4)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
