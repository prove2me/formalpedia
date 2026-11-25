-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:23:52.760582+00:00
-- url     : https://prove2.me/submissions/b494ada2-6da6-4248-abfa-d29c52779ee2

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_teichmuller


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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ K) (h1 : ‖x‖ = 1) :
    ∃ ζ ∈ K, ζ ^ (qK p K - 1) = 1 ∧ ‖x - ζ‖ < 1 :=
  UnramifiedExtensions.exists_teichmuller K hK hx h1
end ReciprocityTheory.DiscreteGroups.LocalClassField
