-- Prove2me | solution 1 for Paper.Hypergraph.trimDemand_fractionalSeparator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:15.919637+00:00
-- url     : https://prove2.me/submissions/92bcb260-488b-4582-8c03-391e29241536

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence
import Theorems.Thm_Paper_Hypergraph_shortest_path_support_card_le_twice_independence
import Theorems.Thm_Paper_Hypergraph_trimDemand_unit
import Theorems.Thm_Paper_Hypergraph_primal_induce_le
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_walk
import Theorems.Thm_Paper_Hypergraph_walk_reachable_induce
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) {ε : ℝ} (hε : 0 < ε)
    (hbudget : ε * (2 * (H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ) ≤ 1 / 2) :
    H.FractionalSeparator A B (trimDemand x ε) := by
  let z := trimDemand x ε
  have hz := H.trimDemand_unit hx.1 ε
  refine ⟨hz, ?_⟩
  intro u hu v hv
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro t (rfl | ⟨p, hp, rfl⟩)
  · exact le_rfl
  let Q := p.support.toFinset
  let R := H.vertices.filter (fun v => x v ≠ 0)
  have huQ : u ∈ (H.induce Q).vertices := mem_inter.mpr
    ⟨hA hu, List.mem_toFinset.mpr p.start_mem_support⟩
  have hpQ := H.walk_reachable_induce p (fun w hw => List.mem_toFinset.mpr hw)
  obtain ⟨q, hq⟩ := hpQ.exists_walk_length_eq_dist
  let T := q.support.toFinset
  have hTV : T ⊆ H.vertices := fun w hw =>
    (mem_inter.mp ((H.induce Q).walk_vertices q huQ w (List.mem_toFinset.mp hw))).1
  have hTQ : T ⊆ Q := fun w hw =>
    (mem_inter.mp ((H.induce Q).walk_vertices q huQ w (List.mem_toFinset.mp hw))).2
  have hxs : 1 ≤ ∑ w ∈ T, x w := by
    have hdist := H.vertexDistance_le_walk (fun w hw => (hx.1 w hw).1) (hA hu)
      (q.mapLe (H.primal_induce_le Q))
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using (hx.2 u hu v hv).trans hdist
  have hzs : 1 ≤ ∑ w ∈ T, z w := by
    by_cases hbig : ∃ w ∈ T, 1 ≤ z w
    · obtain ⟨w, hw, hwz⟩ := hbig
      exact hwz.trans (single_le_sum (fun w hw => (hz w (hTV hw)).1) hw)
    have hsmall : ∀ w ∈ T, z w < 1 := by
      intro w hw
      exact lt_of_not_ge (fun h => hbig ⟨w, hw, h⟩)
    have hcard : (T.filter (fun w => x w ≠ 0)).card ≤ 2 * (H.induce R).independenceNumber :=
      H.shortest_path_support_card_le_twice_independence Q R huQ q hq
        (fun w hw => List.mem_toFinset.mp (mem_filter.mp hw).1)
        (fun w hw => mem_filter.mpr ⟨hTV (mem_filter.mp hw).1, (mem_filter.mp hw).2⟩)
    have hpoint : ∀ w ∈ T, x w ≤ z w / 2 + if x w ≠ 0 then ε else 0 := by
      intro w hw
      by_cases hx0 : x w = 0
      · simp only [hx0, ne_eq, not_true_eq_false, if_false, add_zero]
        exact div_nonneg (hz w (hTV hw)).1 (by norm_num)
      · simp only [hx0, ne_eq, not_false_eq_true, if_true]
        by_cases hlarge : ε ≤ x w
        · have hcap : 2 * x w < 1 := by
            have h := hsmall w hw
            change (if ε ≤ x w then min (2 * x w) 1 else 0) < 1 at h
            rw [if_pos hlarge] at h
            exact (min_lt_iff.mp h).resolve_right (lt_irrefl _)
          have heq : z w = 2 * x w := by simp [z, trimDemand, hlarge, min_eq_left hcap.le]
          rw [heq]
          linarith
        · have heq : z w = 0 := by simp [z, trimDemand, hlarge]
          rw [heq]
          linarith
    have hsum := sum_le_sum hpoint
    rw [sum_add_distrib, ← sum_div, ← sum_filter, sum_const, nsmul_eq_mul] at hsum
    have hc : ((T.filter (fun w => x w ≠ 0)).card : ℝ) ≤ 2 * (H.induce R).independenceNumber := by
      exact_mod_cast hcard
    have hb : ε * (2 * (H.induce R).independenceNumber : ℝ) ≤ 1 / 2 := hbudget
    nlinarith
  exact hzs.trans (sum_le_sum_of_subset_of_nonneg hTQ (fun w hw _ =>
    (hz w (H.walk_vertices p (hA hu) w (List.mem_toFinset.mp hw))).1))
end Paper.Hypergraph
