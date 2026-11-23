-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.IsAbLK.sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:54.946379+00:00
-- url     : https://prove2.me/submissions/6b60da6e-2ea4-4374-9234-535955a50b21

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_sup_eq_inf

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
open Topology
open scoped commutatorElement
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
namespace IsAbLK
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : IsAbLK p K L) (h' : IsAbLK p K L') : IsAbLK p K (L ⊔ L') := by
  refine ⟨h.le.trans le_sup_left, ?_, ?_⟩
  · have := h.fin
    have := h'.fin
    exact IntermediateField.finiteDimensional_sup L L'
  · rw [subG_sup_eq_inf]
    exact le_inf h.comm h'.comm
end IsAbLK
end ReciprocityTheory.DiscreteGroups.LocalClassField
