-- Prove2me | solution 1 for Paper.Hypergraph.finite_tree_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:44.256634+00:00
-- url     : https://prove2.me/submissions/a08692db-8d02-470d-83be-0755f4cbf893

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_finite_rooted_tree_decomposition

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {T : Type*} [Fintype T] [Nonempty T]
    (G : SimpleGraph T) (hG : G.IsTree) (bag : T → Finset ℕ)
    (hsub : ∀ t, bag t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ t, H.edge e ⊆ bag t)
    (hvertex : ∀ v ∈ H.vertices, ∃ t, v ∈ bag t)
    (hrun : ∀ v ∈ H.vertices, (G.induce {t | v ∈ bag t}).Preconnected)
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ t, b (bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∀ t, b (D.bag t) ≤ r := by
  obtain ⟨n, D, _, _, hD⟩ := H.finite_rooted_tree_decomposition G hG bag
    hsub hedge hvertex hrun (Classical.choice inferInstance) ∅ (empty_subset _) b r hwidth
  exact ⟨n, D, hD⟩
end Paper.Hypergraph
