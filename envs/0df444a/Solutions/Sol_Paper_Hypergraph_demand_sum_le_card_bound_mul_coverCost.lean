-- Prove2me | solution 1 for Paper.Hypergraph.demand_sum_le_card_bound_mul_coverCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:39.15769+00:00
-- url     : https://prove2.me/submissions/0aa5401e-1d9c-4007-8349-81a329cf51eb

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
import Theorems.Thm_Paper_Hypergraph_le_coverCost


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ)
    {S : Finset ℕ} (hS : S ⊆ H.vertices) {n : ℕ}
    (hn : ∀ e ∈ H.edges, (S ∩ H.edge e).card ≤ n) :
    (∑ v ∈ S, x v) ≤ n * H.coverCost (restrictDemand x S) := by
  by_cases hn0 : n = 0
  · subst n
    have hempty : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨e, he, hve⟩ := H.no_isolated v (hS hv)
      have hpos : 0 < (S ∩ H.edge e).card := card_pos.mpr ⟨v, mem_inter.mpr ⟨hv, hve⟩⟩
      have := hn e he
      omega
    simp [hempty]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [← div_le_iff₀' hnpos]
  apply H.le_coverCost
  intro y hy
  rw [div_le_iff₀' hnpos]
  have hs : (∑ v ∈ S, x v) ≤ ∑ v ∈ S, ∑ e ∈ H.edges.filter (fun e => v ∈ H.edge e), y e := by
    apply sum_le_sum
    intro v hv
    simpa [restrictDemand, hv] using hy.2 v (hS hv)
  calc
    _ ≤ _ := hs
    _ = ∑ e ∈ H.edges, ((S ∩ H.edge e).card : ℝ) * y e := by
      simp_rw [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      simp [filter_mem_eq_inter, nsmul_eq_mul]
    _ ≤ ∑ e ∈ H.edges, (n : ℝ) * y e := by
      apply sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn e he) (hy.1 e he)
    _ = _ := by rw [mul_sum]
end Paper.Hypergraph
