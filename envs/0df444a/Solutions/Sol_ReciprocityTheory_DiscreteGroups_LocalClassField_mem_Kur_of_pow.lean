-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:55.390714+00:00
-- url     : https://prove2.me/submissions/21137213-f79a-4912-95e8-85f5831c17ea

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kn_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_dvd_qK_pow_sub_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_Kn_of_pow
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Kn_of_pow


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : ¬ p ∣ m) {ζ : PadicAlgCl p}
    (hζ : ζ ^ m = 1) : ζ ∈ MaximalUnramifiedExtension p K := by
  obtain ⟨n, hn, d, hd⟩ := exists_dvd_qK_pow_sub_one hK hm
  exact Kn_le_Kur hn (mem_Kn_of_pow p K (by rw [hd, pow_mul, hζ, one_pow]))
end ReciprocityTheory.DiscreteGroups.LocalClassField
