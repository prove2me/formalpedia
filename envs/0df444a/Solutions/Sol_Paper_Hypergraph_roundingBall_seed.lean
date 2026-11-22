-- Prove2me | solution 1 for Paper.Hypergraph.roundingBall_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:05.993065+00:00
-- url     : https://prove2.me/submissions/a067a272-eee8-42a2-b49d-eb64d5b1d51f

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths
import Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_mono
import Theorems.Thm_Paper_Hypergraph_demand_sum_le_card_bound_mul_coverCost
import Theorems.Thm_Paper_Hypergraph_shortest_induced_path_edge_card
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_walk
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ z ∈ H.vertices, 0 ≤ x z) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {s q : ℝ}
    (hq : ∀ z ∈ H.vertices ∩ Q, x z ≤ q)
    (hout : ∃ v, (H.induce Q).primal.Reachable c v ∧
      s < (H.induce Q).vertexDistance x c v) :
    (s - q) / 2 < H.coverCost (restrictDemand x (H.roundingBall x Q c s)) := by
  obtain ⟨v, hcv, hvd⟩ := hout
  obtain ⟨p, hp⟩ := hcv.exists_walk_length_eq_dist
  have he : ∃ i : ℕ, i ≤ p.length ∧ s < (H.induce Q).vertexDistance x c (p.getVert i) := by
    exact ⟨p.length, le_rfl, by simpa using hvd⟩
  let j := Nat.find he
  have hj := Nat.find_spec he
  change j ≤ p.length ∧ s < (H.induce Q).vertexDistance x c (p.getVert j) at hj
  let T := (p.take j).support.toFinset
  let S := T.erase (p.getVert j)
  have hT : ∀ z ∈ T, z ∈ p.support := by
    intro z hz
    have hz' : z ∈ (p.take j).support := List.mem_toFinset.mp hz
    rw [SimpleGraph.Walk.support_take] at hz'
    exact List.mem_of_mem_take hz'
  have hS : S ⊆ H.roundingBall x Q c s := by
    intro z hz
    obtain ⟨hzj, hzT⟩ := mem_erase.mp hz
    have hzQ := (H.induce Q).walk_vertices p hc z (hT z hzT)
    refine mem_filter.mpr ⟨hzQ, ?_⟩
    obtain ⟨k, hk, hkl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (List.mem_toFinset.mp hzT)
    rw [SimpleGraph.Walk.take_length, min_eq_left hj.1] at hkl
    rw [SimpleGraph.Walk.take_getVert, min_eq_right hkl] at hk
    have hkj : k < j := by
      have : k ≠ j := by intro h; subst k; exact hzj hk.symm
      omega
    have hmin := Nat.find_min he hkj
    have hkle : k ≤ p.length := hkl.trans hj.1
    rw [← hk]
    exact le_of_not_gt fun h => hmin ⟨hkle, h⟩
  have hSV : S ⊆ H.vertices := fun z hz => (mem_inter.mp (mem_filter.mp (hS hz)).1).1
  have hcard : ∀ e ∈ H.edges, (S ∩ H.edge e).card ≤ 2 := by
    intro e he
    exact H.shortest_induced_path_edge_card Q hc p hp (fun z hz => hT z (mem_erase.mp hz).2) he
  have hsum := H.demand_sum_le_card_bound_mul_coverCost x hSV hcard
  have hmono := H.restrictDemand_cost_mono hx hS
  have hjT : p.getVert j ∈ T := List.mem_toFinset.mpr (p.take j).end_mem_support
  have hsumT : (∑ z ∈ S, x z) + x (p.getVert j) = ∑ z ∈ T, x z := sum_erase_add T x hjT
  have hd := (H.induce Q).vertexDistance_le_walk (fun z hz => hx z (mem_inter.mp hz).1) hc (p.take j)
  have hqj := hq (p.getVert j) ((H.induce Q).walk_vertices p hc _ (p.getVert_mem_support j))
  change (H.induce Q).vertexDistance x c (p.getVert j) ≤ ∑ z ∈ T, x z at hd
  norm_num at hsum
  nlinarith [hj.2]
end Paper.Hypergraph
