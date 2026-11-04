-- Prove2me | solution 1 for StrictCQ.CAKKT.theorem_6_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:41:53.404127+00:00
-- url     : https://prove2.me/submissions/42af32fe-d447-4392-801f-4aacbd51177e

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_StrictCQ_CAKKT_Conditions
import Theorems.Thm_StrictCQ_CAKKT_tangentCone_subset_linCone
import Theorems.Thm_StrictCQ_CAKKT_limNormal_subset_polar_linCone
import Theorems.Thm_StrictCQ_CAKKT_polar_limNormal_subset_tangentCone

open Filter Topology
open scoped InnerProductSpace
open StrictCQ.CAKKT

theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible) (hreg : C.CAKKTRegular xs) :
    C.Abadie xs := by
  apply le_antisymm
  · intro d hd
    have hclosed : IsClosed C.feasible := by
      have h1 : ∀ i, Continuous (C.h i) := fun i => (hC.1 i).continuous
      have h2 : ∀ j, Continuous (C.g j) := fun j => (hC.2 j).continuous
      have : C.feasible = (⋂ i, {x | C.h i x = 0}) ∩ ⋂ j, {x | C.g j x ≤ 0} := by
        ext x; simp [Constraints.feasible]
      rw [this]
      exact (isClosed_iInter fun i => isClosed_eq (h1 i) continuous_const).inter
        (isClosed_iInter fun j => isClosed_le (h2 j) continuous_const)
    apply polar_limNormal_subset_tangentCone C.feasible hclosed hxs
    intro v hv
    exact limNormal_subset_polar_linCone C hC hxs hreg hv d hd |>.trans_eq'
      (real_inner_comm _ _)
  · exact tangentCone_subset_linCone C hC hxs
