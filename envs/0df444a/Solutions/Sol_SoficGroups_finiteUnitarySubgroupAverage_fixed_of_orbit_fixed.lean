-- Prove2me | solution 1 for SoficGroups.finiteUnitarySubgroupAverage_fixed_of_orbit_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/dafa74dd-8b27-4ef8-8be6-91b9217f24d5

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
variable {G : Type*} {H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution
    (π : UnitaryRepresentation G H)
    (K J : Subgroup G) [Fintype K] (b : H)
    (horbit : ∀ (k : K) (j : J),
      π (j : G) (π (k : G) b) = π (k : G) b)
    (j : J) :
    π (j : G) (finiteUnitarySubgroupAverage π K b) =
      finiteUnitarySubgroupAverage π K b := by
  classical
  unfold finiteUnitarySubgroupAverage
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact horbit k j
end SoficGroups
