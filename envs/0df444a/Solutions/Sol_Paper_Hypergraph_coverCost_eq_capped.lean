-- Prove2me | solution 1 for Paper.Hypergraph.coverCost_eq_capped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:58.160402+00:00
-- url     : https://prove2.me/submissions/fe181225-4637-49cf-bbea-8a5578aebb0d

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_cover_exists
import Theorems.Thm_Paper_Hypergraph_le_coverCost
import Theorems.Thm_Paper_Hypergraph_cover_cap

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) :
    H.coverCost x = sInf {r | ∃ y, H.Cover x y ∧
      (∀ e ∈ H.edges, y e ≤ 1) ∧ r = ∑ e ∈ H.edges, y e} := by
  obtain ⟨y, hy⟩ := H.cover_exists x
  have hne : {r | ∃ y, H.Cover x y ∧
      (∀ e ∈ H.edges, y e ≤ 1) ∧ r = ∑ e ∈ H.edges, y e}.Nonempty :=
    ⟨_, (fun e => min (y e) 1), H.cover_cap hx hy, fun _ _ => min_le_right _ _, rfl⟩
  have hb : BddBelow {r | ∃ y, H.Cover x y ∧
      (∀ e ∈ H.edges, y e ≤ 1) ∧ r = ∑ e ∈ H.edges, y e} := by
    refine ⟨0, ?_⟩
    rintro r ⟨z, hz, _, rfl⟩
    exact sum_nonneg hz.1
  apply le_antisymm
  · refine le_csInf hne ?_
    rintro r ⟨z, hz, _, rfl⟩
    exact H.coverCost_le hz
  · apply H.le_coverCost
    intro z hz
    exact (csInf_le hb ⟨_, H.cover_cap hx hz, fun _ _ => min_le_right _ _, rfl⟩).trans
      (sum_le_sum (fun _ _ => min_le_left _ _))
end Paper.Hypergraph
