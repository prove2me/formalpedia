-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.Kn_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:34.6888+00:00
-- url     : https://prove2.me/submissions/08c4e7df-3488-48ca-92df-2758dbcf663d

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_le

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
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable (K)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {m n : ℕ} (h : m ∣ n) : Kn p K m ≤ Kn p K n := by
  apply Kn_le K (le_Kn K n)
  intro ζ hζ
  apply mem_Kn_of_pow
  obtain ⟨k, rfl⟩ := h
  obtain ⟨d, hd⟩ : qK p K ^ m - 1 ∣ qK p K ^ (m * k) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (qK p K ^ m) 1 k
  rw [hd, pow_mul, hζ, one_pow]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
