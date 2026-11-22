-- Prove2me | solution 1 for Paper.Hypergraph.twoTerminal_distance_labels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:34.368816+00:00
-- url     : https://prove2.me/submissions/33c6abfe-ad95-431a-b430-a9d5046d92ec

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
import Theorems.Thm_Paper_Hypergraph_demand_le_vertexDistance
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_one
import Theorems.Thm_Paper_Hypergraph_vertexDistance_self_le
import Theorems.Thm_Paper_Hypergraph_vertexDistance_step


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ d : ℕ → ℝ,
      (∀ v ∈ H.vertices, x v ≤ d v ∧ d v ≤ 1) ∧
      (∀ v ∈ A, d v ≤ x v) ∧
      (∀ v ∈ B, 1 ≤ d v) ∧
      (∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v) := by
  by_cases hne : A.Nonempty
  swap
  · refine ⟨fun _ => 1, (fun v hv => ⟨(hx.1 v hv).2, le_rfl⟩), ?_, (fun _ _ => le_rfl), ?_⟩
    · intro v hv
      exact (hne ⟨v, hv⟩).elim
    · intro u hu v hv huv
      have := (hx.1 v hv).1
      linarith
  let d := fun v => A.inf' hne (fun a => H.vertexDistance x a v)
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  have hle : ∀ a ∈ A, ∀ v, d v ≤ H.vertexDistance x a v := by
    intro a ha v
    exact inf'_le _ ha
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro v hv
    constructor
    · apply le_inf'
      intro a ha
      exact H.demand_le_vertexDistance hx.1 (hA ha) hv
    · obtain ⟨a, ha⟩ := hne
      exact (hle a ha v).trans (H.vertexDistance_le_one hn (hA ha))
  · intro a ha
    exact (hle a ha a).trans (H.vertexDistance_self_le hn (hA ha))
  · intro b hb
    apply le_inf'
    intro a ha
    exact hx.2 a ha b hb
  · intro u hu v hv huv
    suffices h : d v - x v ≤ d u by linarith
    apply le_inf'
    intro a ha
    have h := (hle a ha v).trans (H.vertexDistance_step hn (hA ha) hv huv)
    linarith
end Paper.Hypergraph
