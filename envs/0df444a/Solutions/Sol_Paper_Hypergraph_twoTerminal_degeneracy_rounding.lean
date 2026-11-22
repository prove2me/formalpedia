-- Prove2me | solution 1 for Paper.Hypergraph.twoTerminal_degeneracy_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:29.114273+00:00
-- url     : https://prove2.me/submissions/be098a14-142f-4a4c-8019-e13626c595bc

import Definitions.Def_Paper_RoundingAveraging
import Definitions.Def_Paper_RoundingDegeneracy
import Theorems.Thm_Paper_Hypergraph_incidence_elimination_order
import Theorems.Thm_Paper_Hypergraph_degeneracyLevelCover_integrable
import Theorems.Thm_Paper_Hypergraph_degeneracyLevelCover_integral_le
import Theorems.Thm_Paper_Hypergraph_degeneracyLevelCover_covers
import Theorems.Thm_Paper_Hypergraph_coverCost_attained
import Theorems.Thm_Paper_Hypergraph_edge_intervals_common_point
import Theorems.Thm_Paper_Hypergraph_rounding_by_average
import Theorems.Thm_Paper_Hypergraph_twoTerminal_distance_labels


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ (6 * H.degeneracy : ℝ) * H.coverCost x := by
  obtain ⟨d, hd, ha, hb, hstep⟩ := H.twoTerminal_distance_labels hA hx
  obtain ⟨y, hy, _, hcost⟩ := H.coverCost_attained hx.1
  obtain ⟨rank, hinj, hlater⟩ := H.incidence_elimination_order
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  let q := fun e => if he : e ∈ H.edges then (H.edge_intervals_common_point hstep hn he).choose else 0
  have hq : ∀ e ∈ H.edges, ∀ v ∈ H.edge e, d v - x v ≤ q e ∧ q e ≤ d v := by
    intro e he
    simp only [q, dif_pos he]
    exact (H.edge_intervals_common_point hstep hn he).choose_spec
  obtain ⟨S, hS, hsep, hbound⟩ := H.rounding_by_average hA hB ha hb hstep
    (H.degeneracyLevelCover rank x d y q)
    (fun e _ => H.degeneracyLevelCover_integrable rank x d y q e)
    (fun r _ => H.degeneracyLevelCover_covers hn hy hinj hlater hq r)
  refine ⟨S, hS, hsep, hbound.trans ?_⟩
  rw [hcost, mul_sum]
  exact sum_le_sum (fun e he => H.degeneracyLevelCover_integral_le hn hy.1 hlater he)
end Paper.Hypergraph
