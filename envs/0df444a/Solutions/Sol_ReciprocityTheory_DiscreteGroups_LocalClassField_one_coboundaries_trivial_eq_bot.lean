-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.one_coboundaries_trivial_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:21.170996+00:00
-- url     : https://prove2.me/submissions/7a3349bc-406c-4d89-af71-761d5e95f9f5

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (A : Type) [AddCommGroup A] : Gal.B1 (trivRep G A).rho = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨m, rfl⟩
  refine (Submodule.mem_bot _).2 (funext fun g => ?_)
  exact sub_self m
end ReciprocityTheory.DiscreteGroups.LocalClassField
