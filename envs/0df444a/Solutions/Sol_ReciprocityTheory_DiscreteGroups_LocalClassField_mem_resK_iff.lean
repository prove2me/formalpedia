-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_resK_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:17.406612+00:00
-- url     : https://prove2.me/submissions/e64aa874-6c96-4f72-92d3-733f39520fe7

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_mem_resK_iff


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
theorem _root_.solution (c : kbar p) :
    c ∈ resK p K ↔ ∃ x : Obar p, (x : PadicAlgCl p) ∈ K ∧ IsLocalRing.residue (Obar p) x = c :=
  UnramifiedExtensions.mem_resK_iff K c
end ReciprocityTheory.DiscreteGroups.LocalClassField
