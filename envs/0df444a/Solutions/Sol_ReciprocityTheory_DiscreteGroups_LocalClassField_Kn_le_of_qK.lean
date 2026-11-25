-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kn_le_of_qK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:23:29.099894+00:00
-- url     : https://prove2.me/submissions/18eccd02-42f4-4894-a97c-e0d1d554a716

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_of_pow_qK_sub_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_of_pow_qK_sub_one


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) {n m : ℕ} (h : qK p L = qK p K ^ (n * m)) :
    Kn p K n ≤ L := by
  apply UnramifiedExtensions.Kn_le K hKL
  intro ζ hζ
  apply UnramifiedExtensions.mem_of_pow_qK_sub_one L hL
  obtain ⟨d, hd⟩ : qK p K ^ n - 1 ∣ qK p K ^ (n * m) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (qK p K ^ n) 1 m
  rw [h, hd, pow_mul, hζ, one_pow]
end ReciprocityTheory.DiscreteGroups.LocalClassField
