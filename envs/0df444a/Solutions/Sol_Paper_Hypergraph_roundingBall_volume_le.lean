-- Prove2me | solution 1 for Paper.Hypergraph.roundingBall_volume_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:17.91109+00:00
-- url     : https://prove2.me/submissions/fef81720-d5b5-4a19-bc49-1bdd8d4b6b81

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_vertexDistance_le_induce
import Theorems.Thm_Paper_Hypergraph_edgeDistance_le_vertexDistance
import Theorems.Thm_Paper_Hypergraph_edgeDistance_le_one

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ x : ℕ → ℝ} {φ r : ℝ}
    (hγ : ∀ e ∈ H.edges, 0 ≤ γ e) (hx : H.FractionalBalanced γ φ x)
    (Q : Finset ℕ) {c : ℕ} (hc : c ∈ H.vertices ∩ Q) (hr : r < 1) :
    H.edgeVolume γ (H.roundingBall x Q c r) ≤
      φ / (1 - r) * ∑ e ∈ H.edges, γ e := by
  let B := H.roundingBall x Q c r
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v hv => (hx.1 v hv).1
  obtain ⟨e, he, hce⟩ := H.no_isolated c (mem_inter.mp hc).1
  have hd : ∀ f ∈ H.edges, ¬ Disjoint (H.edge f) B → H.edgeDistance x e f ≤ r := by
    intro f hf hmeet
    obtain ⟨v, hvf, hvB⟩ := not_disjoint_iff.mp hmeet
    exact (H.edgeDistance_le_vertexDistance hn he hce hvf).trans
      ((H.vertexDistance_le_induce hn Q (mem_inter.mp hc).1).trans
        (mem_filter.mp hvB).2)
  have hsum : (∑ f ∈ H.edges, γ f * H.edgeDistance x e f) ≤
      (∑ f ∈ H.edges, γ f) - (1 - r) * H.edgeVolume γ B := by
    calc
      _ ≤ ∑ f ∈ H.edges, (γ f - (1 - r) *
          (if ¬ Disjoint (H.edge f) B then γ f else 0)) := by
        apply sum_le_sum
        intro f hf
        split_ifs with hm
        · simpa using mul_le_mul_of_nonneg_left (H.edgeDistance_le_one hn he hf) (hγ f hf)
        · have := mul_le_mul_of_nonneg_left (hd f hf hm) (hγ f hf)
          nlinarith
      _ = _ := by rw [sum_sub_distrib, ← mul_sum]; simp [edgeVolume, sum_filter]
  have hbal := (hx.2 e he).trans hsum
  rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.mpr hr)]
  nlinarith
end Paper.Hypergraph
