-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:44.250172+00:00
-- url     : https://prove2.me/submissions/e5e8d5d8-55d4-4dd7-96ba-c69f097bb0cc

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_eq_one_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_one_of_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0] at hξ; exact zero_ne_one hξ
  have h1 : ζ - ξ = ξ * (ζ / ξ - 1) := by field_simp
  rw [h1, norm_mul, norm_eq_one_of_pow hm0 hξ, one_mul]
  apply norm_sub_one_of_pow hm
  · rw [div_pow, hζ, hξ, div_one]
  · intro h2; exact h ((div_eq_one_iff_eq hξ0).1 h2)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
