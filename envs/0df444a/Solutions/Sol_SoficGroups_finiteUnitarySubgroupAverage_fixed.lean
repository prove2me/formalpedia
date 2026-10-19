-- Prove2me | solution 1 for SoficGroups.finiteUnitarySubgroupAverage_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/383daa53-770e-4766-892b-1fa698b5b6c8

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
    (K : Subgroup G) [Fintype K] (x : H) (g : K) :
    π (g : G) (finiteUnitarySubgroupAverage π K x) =
      finiteUnitarySubgroupAverage π K x := by
  classical
  unfold finiteUnitarySubgroupAverage
  rw [map_smul, map_sum]
  congr 1
  calc
    (∑ k : K, π (g : G) (π (k : G) x)) =
        ∑ k : K, π ((g * k : K) : G) x := by
          apply Finset.sum_congr rfl
          intro k _
          simp [map_mul]
    _ = ∑ k : K, π (k : G) x :=
      Function.Bijective.sum_comp (Group.mulLeft_bijective g)
        (fun k : K => π (k : G) x)
end SoficGroups
