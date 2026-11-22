-- Prove2me | solution 1 for Paper.Hypergraph.cutoff_good_annulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:50.028694+00:00
-- url     : https://prove2.me/submissions/be201934-7b5a-4b91-90b2-7379a898d983

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_RoundingCutoff
import Theorems.Thm_Paper_Hypergraph_cutoff_layer_exists
import Theorems.Thm_Paper_Hypergraph_cutoff_layer_parameters
import Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_le
import Theorems.Thm_Paper_Hypergraph_restrictDemand_cost_mono
import Theorems.Thm_Paper_Hypergraph_roundingBall_mono
import Theorems.Thm_Paper_Hypergraph_roundingBall_no_crossing_edge
import Theorems.Thm_Paper_Hypergraph_roundingBall_seed
import Theorems.Thm_Paper_Hypergraph_separated_restrictDemand_cost_add_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {r q : ℝ} (hr : 0 < r)
    (hK : r / 2 ≤ H.coverCost x)
    (hq0 : 0 ≤ q) (hq : ∀ v ∈ H.vertices ∩ Q, x v ≤ q)
    (hsmall : q < (r / (9 + 2 * Real.logb 2 (H.coverCost x / r))) / 2)
    (hout : ∃ v, (H.induce Q).primal.Reachable c v ∧
      r / 4 < (H.induce Q).vertexDistance x c v) :
    let δ := r / (9 + 2 * Real.logb 2 (H.coverCost x / r))
    ∃ s : ℝ, r / 4 ≤ s ∧ s + 3 * δ / 2 ≤ r ∧
      H.coverCost (restrictDemand x
        (H.roundingBall x Q c (s + 3 * δ / 2) \ H.roundingBall x Q c (s + δ / 2))) ≤
        H.coverCost (restrictDemand x (H.roundingBall x Q c s)) := by
  let δ := r / (9 + 2 * Real.logb 2 (H.coverCost x / r))
  have hδ : 0 < δ := by change q < δ / 2 at hsmall; linarith
  obtain ⟨N, hN, hrad, hbudget, hseednum⟩ := cutoff_layer_parameters hr hK
  let s : ℕ → ℝ := fun i => r / 4 + (i : ℝ) * (3 * δ / 2)
  let B := fun t => H.roundingBall x Q c t
  let a := fun i => H.coverCost (restrictDemand x (B (s i)))
  let ℓ := fun i => H.coverCost (restrictDemand x (B (s (i + 1)) \ B (s i + δ / 2)))
  have hs : ∀ i, s (i + 1) = s i + 3 * δ / 2 := by intro i; dsimp [s]; push_cast; ring
  have hseed : 5 * r / 56 ≤ a 0 := by
    have h := H.roundingBall_seed hx Q hc hq hout
    have hn := hseednum q hsmall
    dsimp [a, B, s]
    simpa using hn.trans h.le
  have hadd : ∀ i < N, a i + ℓ i ≤ a (i + 1) := by
    intro i hi
    have hsep : ∀ e ∈ H.edges, Disjoint (H.edge e) (B (s i)) ∨
        Disjoint (H.edge e) (B (s (i + 1)) \ B (s i + δ / 2)) := by
      intro e he
      rcases H.roundingBall_no_crossing_edge hx Q hc hsmall hq he (s := s i) with h | h
      · exact Or.inl h
      · apply Or.inr
        apply h.mono_right
        intro v hv
        exact mem_sdiff.mpr ⟨(mem_filter.mp (mem_sdiff.mp hv).1).1, (mem_sdiff.mp hv).2⟩
    apply (H.separated_restrictDemand_cost_add_le x _ _ hsep).trans
    apply H.restrictDemand_cost_mono hx
    apply union_subset
    · apply H.roundingBall_mono
      rw [hs]
      linarith
    · exact sdiff_subset
  have hupper : a N ≤ H.coverCost x := H.restrictDemand_cost_le hx _
  obtain ⟨i, hi, hgood⟩ := cutoff_layer_exists a ℓ N hseed hbudget hupper hadd
  refine ⟨s i, ?_, ?_, ?_⟩
  · dsimp [s]
    have : 0 ≤ (i : ℝ) * (3 * δ / 2) := mul_nonneg (Nat.cast_nonneg _) (by positivity)
    linarith
  · have hiN : (i + 1 : ℝ) ≤ N := by exact_mod_cast (show i + 1 ≤ N by omega)
    have hh := mul_le_mul_of_nonneg_right hiN (show 0 ≤ 3 * δ / 2 by positivity)
    change r / 4 + (N : ℝ) * (3 * δ / 2) ≤ r at hrad
    dsimp [s]
    linarith
  · simpa only [ℓ, a, hs] using hgood
end Paper.Hypergraph
