-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_of_pow_qK_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:09:25.973326+00:00
-- url     : https://prove2.me/submissions/ad5fb883-044b-4fa2-b9d5-598712dc78d2

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K - 1) = 1) : ζ ∈ K :=
  UnramifiedExtensions.mem_of_pow_qK_sub_one K hK hζ
end ReciprocityTheory.DiscreteGroups.LocalClassField
