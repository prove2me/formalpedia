-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.finiteUnitarySubgroupAverage_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/964e62b1-683c-4f85-923d-334ef06ec87c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace SoficGroups.ErshovJaikinFiniteSpectral
theorem _root_.solution
    (π : SoficGroups.UnitaryRepresentation G H)
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
end SoficGroups.ErshovJaikinFiniteSpectral
