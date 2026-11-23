-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isAbLK_of_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:06.247506+00:00
-- url     : https://prove2.me/submissions/1fe76ff9-2246-43c6-b8ef-2922d7445b37

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim

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
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] (g₀ : GalLK p K L)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) : IsAbLK p K L := by
  refine ⟨h, hL, Subgroup.Normal.quotient_commutative_iff_commutator_le.1 ⟨⟨fun a b => ?_⟩⟩⟩
  obtain ⟨i, rfl⟩ := hg a
  obtain ⟨j, rfl⟩ := hg b
  exact (zpow_mul_comm g₀ i j)
end ReciprocityTheory.DiscreteGroups.LocalClassField
