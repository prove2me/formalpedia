-- Prove2me | solution 1 for Paper.Hypergraph.modular_le_coverCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:37.746818+00:00
-- url     : https://prove2.me/submissions/0050ba62-63a3-415d-bb42-0f8d35f0aa2c

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_le_coverCost
import Theorems.Thm_Paper_Hypergraph_sum_incidence_swap

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {w : ℕ → ℝ} (hw : H.ModularWeight w)
    (x : ℕ → ℝ) : (∑ v ∈ H.vertices, w v * x v) ≤ H.coverCost x := by
  apply H.le_coverCost
  intro y hy
  calc
    (∑ v ∈ H.vertices, w v * x v) ≤
        ∑ v ∈ H.vertices, w v * (∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e) :=
      sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hy.2 v hv) (hw.1 v))
    _ = ∑ v ∈ H.vertices, ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), w v * y e := by
      simp_rw [mul_sum]
    _ = ∑ e ∈ H.edges, ∑ v ∈ H.edge e, w v * y e := H.sum_incidence_swap _
    _ ≤ ∑ e ∈ H.edges, y e := by
      apply sum_le_sum
      intro e he
      rw [← sum_mul]
      exact mul_le_of_le_one_left (hy.1 e he) (hw.2 e he)
end Paper.Hypergraph
