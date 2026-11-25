-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.IsFrobOn.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:04.168059+00:00
-- url     : https://prove2.me/submissions/4d74c906-81ca-492e-a7cd-bfc84d4e2678

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kn_mono
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_Kn_mono


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {m n : ℕ} (h : m ∣ n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) : IsFrobOn p K m φ :=
  fun x hx hx1 => hφ x (Kn_mono p K hK h hx) hx1
end IsFrobOn
end ReciprocityTheory.DiscreteGroups.LocalClassField
