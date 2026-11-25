-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.exists_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:56:12.570431+00:00
-- url     : https://prove2.me/submissions/f680b73c-7f5c-4a0c-8636-3d984ba8ffc6

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_pow_sub_one_ne_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_apply_root
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_eqOn_Kn_of_primitive
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrobOn_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_pow_of_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_primitiveRoot


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
namespace IsFrobOn
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) (σ : GK p K) : ∃ i < n, ∀ x ∈ Kn p K n, σ x = (φ ^ i) x := by
  rw [isFrobOn_iff p K hK hn] at hφ
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ₀.pow_eq_one
  refine ⟨i, hi, fun x hx => UnramifiedExtensions.eqOn_Kn_of_primitive hm0 hζ₀ ?_ hx⟩
  rw [h, UnramifiedExtensions.pow_apply_root hφ i ζ₀ hζ₀.pow_eq_one]
end IsFrobOn
end ReciprocityTheory.DiscreteGroups.LocalClassField
