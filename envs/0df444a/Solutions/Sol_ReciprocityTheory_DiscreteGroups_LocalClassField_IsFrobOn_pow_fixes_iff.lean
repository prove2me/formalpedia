-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.pow_fixes_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:01:23.441994+00:00
-- url     : https://prove2.me/submissions/f04cd766-f7ec-4b25-8228-28a769ffd408

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_qK_pow_sub_one_ne_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_apply_root
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_eqOn_Kn_of_primitive
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_pow_sub_one_dvd_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrobOn_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_primitiveRoot
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_one_lt_qK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kn_of_pow
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
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
namespace IsFrobOn
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) (i : ℕ) : (∀ x ∈ Kn p K n, (φ ^ i) x = x) ↔ n ∣ i := by
  rw [isFrobOn_iff p K hK hn] at hφ
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hζ1 := hζ₀.pow_eq_one
  have hζ0 : ζ₀ ≠ 0 := hζ₀.ne_zero hm0
  have h1 : 1 ≤ qK p K ^ i := Nat.one_le_pow _ _ (by omega)
  have key : (φ ^ i) ζ₀ = ζ₀ ↔ n ∣ i := by
    rw [UnramifiedExtensions.pow_apply_root hφ i ζ₀ hζ1, ← UnramifiedExtensions.pow_sub_one_dvd_iff hq, ← hζ₀.pow_eq_one_iff_dvd]
    have h2 : ζ₀ ^ (qK p K ^ i) = ζ₀ ^ (qK p K ^ i - 1) * ζ₀ := by
      rw [← pow_succ, Nat.sub_add_cancel h1]
    rw [h2]
    constructor
    · intro h
      exact mul_right_cancel₀ hζ0 (by rw [h, one_mul])
    · intro h
      rw [h, one_mul]
  rw [← key]
  constructor
  · intro h
    exact h ζ₀ (mem_Kn_of_pow p K hζ1)
  · intro h x hx
    exact UnramifiedExtensions.eqOn_Kn_of_primitive (τ := 1) hm0 hζ₀ h hx
end IsFrobOn
end ReciprocityTheory.DiscreteGroups.LocalClassField
