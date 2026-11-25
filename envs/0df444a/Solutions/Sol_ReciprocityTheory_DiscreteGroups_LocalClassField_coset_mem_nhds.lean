-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.coset_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:32.850411+00:00
-- url     : https://prove2.me/submissions/305f8903-efcb-4332-9be4-2ac156637a60

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isOpenMap_toAbK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isOpen_subG


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
theorem _root_.solution (hL : IsAbLK p K L) (g : GK p K) :
    toAbK p K '' {g' | g⁻¹ * g' ∈ subG p K L} ∈ 𝓝 (toAbK p K g) := by
  refine (isOpenMap_toAbK _ ?_).mem_nhds ⟨g, ?_, rfl⟩
  · exact (isOpen_subG hL.fin).preimage (continuous_const.mul continuous_id)
  · show g⁻¹ * g ∈ subG p K L
    rw [inv_mul_cancel]; exact one_mem _
end ReciprocityTheory.DiscreteGroups.LocalClassField
