-- Prove2me | solution 1 for Paper.Hypergraph.coverCost_induce_restrictDemand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:01.405795+00:00
-- url     : https://prove2.me/submissions/1473bdc2-bbd3-41c1-8c52-10a9f6643a4f

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Theorems.Thm_Paper_Hypergraph_incident_edges_induce
import Theorems.Thm_Paper_Hypergraph_le_coverCost


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (z : ℕ → ℝ) (Q : Finset ℕ) :
    (H.induce Q).coverCost z = H.coverCost (restrictDemand z Q) := by
  apply le_antisymm
  · apply H.le_coverCost
    intro y hy
    have hy' : (H.induce Q).Cover z y := by
      refine ⟨fun e he => hy.1 e (mem_filter.mp he).1, ?_⟩
      intro v hv
      rw [H.incident_edges_induce (mem_inter.mp hv).2]
      simpa [restrictDemand, (mem_inter.mp hv).2] using hy.2 v (mem_inter.mp hv).1
    exact ((H.induce Q).coverCost_le hy').trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hy.1 e he))
  · apply (H.induce Q).le_coverCost
    intro y hy
    let y' := fun e => if e ∈ (H.induce Q).edges then y e else 0
    have hy0 : ∀ e, 0 ≤ y' e := by
      intro e
      dsimp [y']
      split_ifs with he
      · exact hy.1 e he
      · exact le_rfl
    have hy' : H.Cover (restrictDemand z Q) y' := by
      refine ⟨fun e _ => hy0 e, ?_⟩
      intro v hv
      by_cases hvQ : v ∈ Q
      · have h := hy.2 v (mem_inter.mpr ⟨hv, hvQ⟩)
        rw [← H.incident_edges_induce hvQ]
        simp only [restrictDemand, if_pos hvQ]
        convert h using 1
        apply sum_congr rfl
        intro e he
        simp [y', (mem_filter.mp he).1]
      · simp only [restrictDemand, if_neg hvQ]
        exact sum_nonneg fun e _ => hy0 e
    apply (H.coverCost_le hy').trans_eq
    dsimp [y']
    rw [← sum_filter]
    congr 1
    ext e
    simp [induce]
end Paper.Hypergraph
