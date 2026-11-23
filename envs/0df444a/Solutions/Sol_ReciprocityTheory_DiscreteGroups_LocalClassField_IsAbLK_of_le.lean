-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.IsAbLK.of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:00.138061+00:00
-- url     : https://prove2.me/submissions/c752b711-3b0a-4b76-9089-b1619056ad54

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti


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
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h' : IsAbLK p K L') (hK : K ≤ L) (hL : L ≤ L') : IsAbLK p K L := by
  refine ⟨hK, ?_, h'.comm.trans (subG_anti hL)⟩
  have := h'.fin
  exact Module.Finite.of_injective (IntermediateField.inclusion hL).toLinearMap
    (IntermediateField.inclusion hL).injective
end IsAbLK
end ReciprocityTheory.DiscreteGroups.LocalClassField
