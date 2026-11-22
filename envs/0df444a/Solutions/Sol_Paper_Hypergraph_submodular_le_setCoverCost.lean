-- Prove2me | solution 1 for Paper.Hypergraph.submodular_le_setCoverCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:26.865032+00:00
-- url     : https://prove2.me/submissions/c87b0046-c7f5-443d-bab8-c3db2e6c32eb

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_submodular_support
import Theorems.Thm_Paper_Hypergraph_modular_le_coverCost

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {b : Finset ℕ → ℝ}
    (hb : H.SubmodularWeight b) {S : Finset ℕ} (hS : S ⊆ H.vertices) :
    b S ≤ H.setCoverCost S := by
  obtain ⟨w, hw, hout, hsum, hdom⟩ := submodular_support S b hb.1
    (fun A hA B hB hAB => hb.2.1 A (hA.trans hS) B (hB.trans hS) hAB)
    (fun A hA B hB => hb.2.2.1 A (hA.trans hS) B (hB.trans hS))
  have hweight : H.ModularWeight w := by
    refine ⟨hw, ?_⟩
    intro e he
    have hrestrict : modularValue w (H.edge e) = modularValue w (H.edge e ∩ S) := by
      symm
      apply sum_subset inter_subset_left
      intro v hv hnot
      exact hout v (fun hvS => hnot (mem_inter.mpr ⟨hv, hvS⟩))
    change modularValue w (H.edge e) ≤ 1
    rw [hrestrict]
    exact (hdom _ inter_subset_right).trans
      ((hb.2.1 _ (inter_subset_left.trans (H.edge_subset e he)) _
        (H.edge_subset e he) inter_subset_left).trans (hb.2.2.2 e he))
  calc
    b S = modularValue w S := hsum.symm
    _ = ∑ v ∈ H.vertices, w v * indicator S v := by
      simp only [modularValue, indicator, mul_ite, mul_one, mul_zero, ← sum_filter]
      congr 1
      ext v
      simp only [mem_filter]
      exact ⟨fun hv => ⟨hS hv, hv⟩, And.right⟩
    _ ≤ H.setCoverCost S := H.modular_le_coverCost hweight _
end Paper.Hypergraph
