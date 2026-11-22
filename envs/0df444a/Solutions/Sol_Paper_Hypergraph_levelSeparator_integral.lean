-- Prove2me | solution 1 for Paper.Hypergraph.levelSeparator_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:49.300563+00:00
-- url     : https://prove2.me/submissions/aea2b995-f3e4-4b62-ab7c-2ecce29eccae

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
import Theorems.Thm_Paper_Hypergraph_primal_induce_le
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x d : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices)
    (ha : ∀ v ∈ A, d v ≤ x v) (hb : ∀ v ∈ B, 1 ≤ d v)
    (hstep : ∀ u ∈ H.vertices, ∀ v ∈ H.vertices, H.primal.Adj u v → d v ≤ d u + x v)
    {r : ℝ} (hr : 0 < r ∧ r < 1) : H.IntegralSeparator A B (H.levelSeparator x d r) := by
  let S := H.levelSeparator x d r
  have hlow : ∀ v ∈ A \ S, d v < r := by
    intro v hv
    have hvA := (mem_sdiff.mp hv).1
    have hvout := (mem_sdiff.mp hv).2
    by_contra h
    have hd : r ≤ d v := le_of_not_gt h
    have hxa := ha v hvA
    have hxv : x v ≠ 0 := by intro h0; rw [h0] at hxa; linarith [hr.1]
    exact hvout (mem_filter.mpr ⟨hA hvA, hxv, by linarith [hr.1], hd⟩)
  refine ⟨filter_subset _ _, ?_⟩
  intro u hu v hv huv
  let J := H.induce (H.vertices \ S)
  have huJ : u ∈ J.vertices := mem_inter.mpr ⟨hA (mem_sdiff.mp hu).1,
    mem_sdiff.mpr ⟨hA (mem_sdiff.mp hu).1, (mem_sdiff.mp hu).2⟩⟩
  have hclosed : ∀ a ∈ J.vertices.filter (fun w => d w < r), ∀ b ∈ J.vertices,
      J.primal.Adj a b → b ∈ J.vertices.filter (fun w => d w < r) := by
    intro a ha b hb hab
    apply mem_filter.mpr ⟨hb, ?_⟩
    have ha' := mem_filter.mp ha
    have hadj := H.primal_induce_le (H.vertices \ S) hab
    have hds := hstep a (mem_inter.mp ha'.1).1 b (mem_inter.mp hb).1 hadj
    by_contra h
    have hrd : r ≤ d b := le_of_not_gt h
    have hxb : x b ≠ 0 := by intro h0; rw [h0] at hds; linarith
    exact (mem_sdiff.mp (mem_inter.mp hb).2).2
      (mem_filter.mpr ⟨(mem_inter.mp hb).1, hxb, by linarith, hrd⟩)
  have hvlow : v ∈ J.vertices.filter (fun w => d w < r) := by
    -- Propagate the strict lower level along a surviving path.
    obtain ⟨p⟩ := huv
    have hstart : d u < r := hlow u hu
    suffices h : d v < r from mem_filter.mpr
      ⟨mem_inter.mpr ⟨hB (mem_sdiff.mp hv).1,
        mem_sdiff.mpr ⟨hB (mem_sdiff.mp hv).1, (mem_sdiff.mp hv).2⟩⟩, h⟩
    clear hu hlow hv
    induction p with
    | nil => exact hstart
    | @cons a b v hab p ih =>
      have hbJ := J.walk_vertices (.cons hab p) huJ b (by simp)
      have hbLow := hclosed a (mem_filter.mpr ⟨huJ, hstart⟩) b hbJ hab
      exact ih hbJ (mem_filter.mp hbLow).2
  have hlarge := hb v (mem_sdiff.mp hv).1
  have := (mem_filter.mp hvlow).2
  linarith [hr.2]
end Paper.Hypergraph
