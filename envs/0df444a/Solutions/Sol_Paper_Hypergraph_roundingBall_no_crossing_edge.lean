-- Prove2me | solution 1 for Paper.Hypergraph.roundingBall_no_crossing_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:44.229103+00:00
-- url     : https://prove2.me/submissions/3f326fe4-0d4c-4eb3-97e7-cdc45487dd3b

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
import Theorems.Thm_Paper_Hypergraph_vertexDistance_step
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {s g q : ℝ} (hqg : q < g)
    (hq : ∀ v ∈ H.vertices ∩ Q, x v ≤ q) {e : ℕ} (he : e ∈ H.edges) :
    Disjoint (H.edge e) (H.roundingBall x Q c s) ∨
      Disjoint (H.edge e) ((H.vertices ∩ Q) \ H.roundingBall x Q c (s + g)) := by
  by_contra hn
  obtain ⟨hA, hB⟩ := not_or.mp hn
  obtain ⟨u, hue, huA⟩ := not_disjoint_iff.mp hA
  obtain ⟨v, hve, hvB⟩ := not_disjoint_iff.mp hB
  have huQ := (mem_filter.mp huA).1
  have hvQ := (mem_sdiff.mp hvB).1
  have hud := (mem_filter.mp huA).2
  have hvd : s + g < (H.induce Q).vertexDistance x c v := by
    apply lt_of_not_ge
    intro h
    exact (mem_sdiff.mp hvB).2 (mem_filter.mpr ⟨hvQ, h⟩)
  have huv : u ≠ v := by
    intro h
    subst v
    have := hq u huQ
    have := hx u (mem_inter.mp huQ).1
    linarith
  have hadj : (H.induce Q).primal.Adj u v := by
    apply (H.primal_induce_adj Q (mem_inter.mp huQ).2 (mem_inter.mp hvQ).2).2
    exact ⟨huv, e, he, hue, hve⟩
  have hs := (H.induce Q).vertexDistance_step
    (fun z hz => hx z (mem_inter.mp hz).1) hc hvQ hadj
  have := hq v hvQ
  linarith
end Paper.Hypergraph
