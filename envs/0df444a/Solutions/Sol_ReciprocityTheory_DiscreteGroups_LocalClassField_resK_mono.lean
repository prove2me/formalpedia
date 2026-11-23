-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.resK_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:14.896731+00:00
-- url     : https://prove2.me/submissions/30ed7a33-286d-496d-bbba-1b5370e056a1

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_resK_mono


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
theorem _root_.solution {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) : resK p K ≤ resK p L :=
  UnramifiedExtensions.resK_mono h
end ReciprocityTheory.DiscreteGroups.LocalClassField
