-- Prove2me | solution 1 for Paper.Hypergraph.cover_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:03.948695+00:00
-- url     : https://prove2.me/submissions/04a2bad8-2713-47d6-b0c9-8791e0619b85

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_le_coverCost
import Theorems.Thm_Paper_Hypergraph_incident_edges_induce

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {X W : Finset ℕ}
    (hXW : X ⊆ W) :
    (H.induce W).setCoverCost X = H.setCoverCost X := by
  change (H.induce W).coverCost (indicator X) = H.coverCost (indicator X)
  apply le_antisymm
  · apply H.le_coverCost
    intro y hy
    have hy' : (H.induce W).Cover (indicator X) y := by
      refine ⟨fun e he => hy.1 e (mem_filter.mp he).1, ?_⟩
      intro v hv
      rw [H.incident_edges_induce (mem_inter.mp hv).2]
      exact hy.2 v (mem_inter.mp hv).1
    exact ((H.induce W).coverCost_le hy').trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hy.1 e he))
  · apply (H.induce W).le_coverCost
    intro y hy
    let y' : ℕ → ℝ := fun e => if e ∈ (H.induce W).edges then y e else 0
    have hy'nonneg : ∀ e, 0 ≤ y' e := by
      intro e
      dsimp [y']
      split_ifs with he
      · exact hy.1 e he
      · exact le_rfl
    have hy' : H.Cover (indicator X) y' := by
      refine ⟨fun e _ => hy'nonneg e, ?_⟩
      intro v hv
      by_cases hvW : v ∈ W
      · have hcov := hy.2 v (mem_inter.mpr ⟨hv, hvW⟩)
        rw [← H.incident_edges_induce hvW]
        convert hcov using 1
        apply sum_congr rfl
        intro e he
        simp only [y', if_pos (mem_filter.mp he).1]
      · have hvX : v ∉ X := fun h => hvW (hXW h)
        simp only [indicator, if_neg hvX]
        exact sum_nonneg (fun e _ => hy'nonneg e)
    calc
      H.coverCost (indicator X) ≤ ∑ e ∈ H.edges, y' e := H.coverCost_le hy'
      _ = ∑ e ∈ (H.induce W).edges, y e := by
        dsimp [y']
        rw [← sum_filter]
        congr 1
        ext e
        simp only [induce, mem_filter, and_self_left]
end Paper.Hypergraph
