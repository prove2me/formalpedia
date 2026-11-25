-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.map_mem_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:00.317813+00:00
-- url     : https://prove2.me/submissions/46feb1ad-1fec-4bda-9c48-f4be653f89d0

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_map_mem_Kn


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
theorem _root_.solution (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n :=
  UnramifiedExtensions.map_mem_Kn K n σ hx
end ReciprocityTheory.DiscreteGroups.LocalClassField
