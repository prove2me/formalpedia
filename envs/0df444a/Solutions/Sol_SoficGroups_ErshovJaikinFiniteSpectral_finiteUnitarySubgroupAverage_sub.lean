-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.finiteUnitarySubgroupAverage_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/1267feef-4c47-44f8-839a-fae279042676

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
    (K : Subgroup G) [Fintype K] (x : H) :
    finiteUnitarySubgroupAverage π K x - x =
      (Fintype.card K : ℂ)⁻¹ •
        ∑ k : K, (π (k : G) x - x) := by
  classical
  have hcard : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteUnitarySubgroupAverage
  rw [Finset.sum_sub_distrib, smul_sub]
  have hconst :
      (Fintype.card K : ℂ)⁻¹ • (∑ _k : K, x) = x := by
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hcard]
  rw [hconst]
end SoficGroups.ErshovJaikinFiniteSpectral
