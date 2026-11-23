-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.h_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:30.777305+00:00
-- url     : https://prove2.me/submissions/baeaed43-c52a-4e5e-92af-d348d3d00471

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution (ρ : Representation k G M) (g : G) :
    h ρ g = (Nat.card (TateZerothCohomology ρ g) : ℚ) / (Nat.card (H1 ρ g) : ℚ) := rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
