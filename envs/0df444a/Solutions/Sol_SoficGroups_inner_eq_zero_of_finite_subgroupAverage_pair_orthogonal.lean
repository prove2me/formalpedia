-- Prove2me | solution 1 for SoficGroups.inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/cf002498-88de-4582-bc1d-c30545bc048c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_finiteUnitarySubgroupAverage_fixed
import Theorems.Thm_SoficGroups_finiteUnitarySubgroupAverage_fixed
import Theorems.Thm_SoficGroups_inner_finiteUnitarySubgroupAverage_of_fixed_left
import Theorems.Thm_SoficGroups_finiteUnitarySubgroupAverage_fixed_of_orbit_fixed

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
    (K J : Subgroup G) [Fintype K] (a b : H)
    (ha : ∀ k : K, π (k : G) a = a)
    (horbit : ∀ (k : K) (j : J),
      π (j : G) (π (k : G) b) = π (k : G) b)
    (horth : ∀ z : H,
      (∀ k : K, π (k : G) z = z) →
      (∀ j : J, π (j : G) z = z) →
      inner ℂ a z = 0) :
    inner ℂ a b = 0 := by
  let z : H := finiteUnitarySubgroupAverage π K b
  have hzK : ∀ k : K, π (k : G) z = z :=
    finiteUnitarySubgroupAverage_fixed π K b
  have hzJ : ∀ j : J, π (j : G) z = z :=
    finiteUnitarySubgroupAverage_fixed_of_orbit_fixed
      π K J b horbit
  calc
    inner ℂ a b = inner ℂ a z :=
      (inner_finiteUnitarySubgroupAverage_of_fixed_left
        π K a b ha).symm
    _ = 0 := horth z hzK hzJ
end SoficGroups
