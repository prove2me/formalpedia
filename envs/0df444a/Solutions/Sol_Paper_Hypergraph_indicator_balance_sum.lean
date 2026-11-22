-- Prove2me | solution 1 for Paper.Hypergraph.indicator_balance_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:37.804315+00:00
-- url     : https://prove2.me/submissions/137760c8-5762-4549-b817-a05a91611bad

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_edgeDistance_indicator_component

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (γ : ℕ → ℝ) (S : Finset ℕ)
    {e u : ℕ} (he : e ∈ H.edges) (hue : u ∈ H.edge e)
    {K : Finset ℕ} (hK : K ∈ (H.induce (H.vertices \ S)).components) (huK : u ∈ K) :
    (∑ f ∈ H.edges, γ f * H.edgeDistance (indicator S) e f) =
      (∑ f ∈ H.edges, γ f) -
        ∑ f ∈ H.edges.filter (fun f => ¬ Disjoint (H.edge f) K), γ f := by
  calc
    _ = ∑ f ∈ H.edges, γ f * (if ¬ Disjoint (H.edge f) K then 0 else 1) := by
      apply sum_congr rfl
      intro f hf
      rw [H.edgeDistance_indicator_component S he hf hue hK huK]
    _ = _ := by
      rw [sum_filter, ← sum_sub_distrib]
      apply sum_congr rfl
      intro f hf
      split_ifs <;> ring
end Paper.Hypergraph
