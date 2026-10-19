-- Prove2me | solution 1 for SoficGroups.inner_finiteUnitarySubgroupAverage_of_fixed_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/6ff3b7fb-fda4-4351-a735-9d3cab40e653

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
    (K : Subgroup G) [Fintype K] (a b : H)
    (ha : ∀ k : K, π (k : G) a = a) :
    inner ℂ a (finiteUnitarySubgroupAverage π K b) =
      inner ℂ a b := by
  classical
  have hcard : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hterm (k : K) :
      inner ℂ a (π (k : G) b) = inner ℂ a b := by
    calc
      inner ℂ a (π (k : G) b) =
          inner ℂ (π (k : G) a) (π (k : G) b) := by rw [ha k]
      _ = inner ℂ a b := (π (k : G)).inner_map_map a b
  unfold finiteUnitarySubgroupAverage
  rw [inner_smul_right, inner_sum]
  simp_rw [hterm]
  simp [hcard]
end SoficGroups
