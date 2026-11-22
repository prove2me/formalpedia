-- Prove2me | solution 1 for Paper.Hypergraph.separated_restrictDemand_cost_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:00.423118+00:00
-- url     : https://prove2.me/submissions/2656dabe-121b-41f6-b663-f95ea7f8fb37

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
import Theorems.Thm_Paper_Hypergraph_restrictDemand_restrict_of_subset
import Theorems.Thm_Paper_Hypergraph_sum_restrictDemand_cost_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ)
    (A B : Finset ℕ)
    (hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) A ∨ Disjoint (H.edge e) B) :
    H.coverCost (restrictDemand x A) + H.coverCost (restrictDemand x B) ≤
      H.coverCost (restrictDemand x (A ∪ B)) := by
  let P : Bool → Finset ℕ := fun b => if b then B else A
  have hs : ∀ e ∈ H.edges, ∀ i ∈ (univ : Finset Bool), ∀ j ∈ (univ : Finset Bool),
      ¬ Disjoint (H.edge e) (P i) → ¬ Disjoint (H.edge e) (P j) → i = j := by
    intro e he i hi j hj hmi hmj
    have h := hsep e he
    cases i <;> cases j <;> simp_all [P] <;>
      rcases hsep e he with h | h <;> contradiction
  have h := H.sum_restrictDemand_cost_le univ P (restrictDemand x (A ∪ B)) hs
  simpa [P, restrictDemand_restrict_of_subset x (subset_union_left : A ⊆ A ∪ B),
    restrictDemand_restrict_of_subset x (subset_union_right : B ⊆ A ∪ B), add_comm] using h
end Paper.Hypergraph
