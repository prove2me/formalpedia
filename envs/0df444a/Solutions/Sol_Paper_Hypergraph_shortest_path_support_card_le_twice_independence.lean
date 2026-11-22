-- Prove2me | solution 1 for Paper.Hypergraph.shortest_path_support_card_le_twice_independence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:34.812766+00:00
-- url     : https://prove2.me/submissions/dc83cdc6-0e71-4712-991f-455e58d468da

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence
import Theorems.Thm_Paper_Hypergraph_independent_card_le
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj
import Theorems.Thm_Paper_Hypergraph_primal_induce_le
import Theorems.Thm_Paper_Hypergraph_shortest_path_prefix_distance
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph)
    (Q R : Finset ℕ) {u v : ℕ} (hu : u ∈ (H.induce Q).vertices)
    (p : (H.induce Q).primal.Walk u v) (hp : p.length = (H.induce Q).primal.dist u v)
    {S : Finset ℕ} (hS : ∀ w ∈ S, w ∈ p.support) (hR : S ⊆ R) :
    S.card ≤ 2 * (H.induce R).independenceNumber := by
  let J := H.induce Q
  let c := fun w => J.primal.dist u w
  have hinj : ∀ a ∈ S, ∀ b ∈ S, c a = c b → a = b := by
    intro a ha b hb heq
    obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hS a ha)
    obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hS b hb)
    have hdi := shortest_path_prefix_distance p hp hil
    have hdj := shortest_path_prefix_distance p hp hjl
    rw [hi] at hdi
    rw [hj] at hdj
    have hij : i = j := by change (H.induce Q).primal.dist u a = (H.induce Q).primal.dist u b at heq; omega
    exact hi.symm.trans ((congrArg p.getVert hij).trans hj)
  have hpart (k : ℕ) : (S.filter (fun w => c w % 2 = k)).card ≤ (H.induce R).independenceNumber := by
    apply (H.induce R).independent_card_le
    · intro w hw
      have hwS := (mem_filter.mp hw).1
      exact mem_inter.mpr ⟨(mem_inter.mp (J.walk_vertices p hu w (hS w hwS))).1, hR hwS⟩
    · intro a ha b hb hab
      obtain ⟨haS, hac⟩ := mem_filter.mp ha
      obtain ⟨hbS, hbc⟩ := mem_filter.mp hb
      have haJ := J.walk_vertices p hu a (hS a haS)
      have hbJ := J.walk_vertices p hu b (hS b hbS)
      have hadj : J.primal.Adj a b :=
        (H.primal_induce_adj Q (mem_inter.mp haJ).2 (mem_inter.mp hbJ).2).mpr
          (H.primal_induce_le R hab)
      have h₁ := hadj.reachable.dist_triangle_right u
      have h₂ := hadj.symm.reachable.dist_triangle_right u
      rw [J.primal.dist_eq_one_iff_adj.mpr hadj] at h₁
      rw [J.primal.dist_eq_one_iff_adj.mpr hadj.symm] at h₂
      have heq : c a = c b := by dsimp [c] at *; omega
      exact hab.ne (hinj a haS b hbS heq)
  have hcover : S = S.filter (fun w => c w % 2 = 0) ∪ S.filter (fun w => c w % 2 = 1) := by
    ext w
    simp only [mem_union, mem_filter]
    have := Nat.mod_lt (c w) (by decide : 0 < 2)
    by_cases hw : w ∈ S
    · simp only [hw, true_and, true_iff]
      omega
    · simp [hw]
  calc
    S.card ≤ (S.filter (fun w => c w % 2 = 0)).card + (S.filter (fun w => c w % 2 = 1)).card := by
      conv_lhs => rw [hcover]
      exact card_union_le _ _
    _ ≤ _ := by have h0 := hpart 0; have h1 := hpart 1; omega
end Paper.Hypergraph
