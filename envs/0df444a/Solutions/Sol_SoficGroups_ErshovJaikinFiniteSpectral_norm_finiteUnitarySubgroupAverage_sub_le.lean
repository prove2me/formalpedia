-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.norm_finiteUnitarySubgroupAverage_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/1f267034-a31a-4b3c-bf6a-f6ac6c21cf79

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_finiteUnitarySubgroupAverage_sub

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
    ‖finiteUnitarySubgroupAverage π K x - x‖ ≤
      (Fintype.card K : ℝ)⁻¹ *
        ∑ k : K, ‖π (k : G) x - x‖ := by
  classical
  rw [finiteUnitarySubgroupAverage_sub, norm_smul, norm_inv,
    Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left
    (norm_sum_le Finset.univ (fun k : K => π (k : G) x - x))
    (by positivity)
end SoficGroups.ErshovJaikinFiniteSpectral
