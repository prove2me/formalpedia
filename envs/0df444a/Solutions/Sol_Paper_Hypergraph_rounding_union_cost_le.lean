-- Prove2me | solution 1 for Paper.Hypergraph.rounding_union_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:20.370962+00:00
-- url     : https://prove2.me/submissions/1997ae3d-4320-47f8-a64a-4630a4168099

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates
import Theorems.Thm_Paper_Hypergraph_roundingThreshold_cost_le
import Theorems.Thm_Paper_Hypergraph_sum_restrictDemand_cost_le
import Theorems.Thm_Paper_Hypergraph_setCoverCost_biUnion_le
import Theorems.Thm_Paper_Hypergraph_setCoverCost_union_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {ι : Type*}
    (I : Finset ι) (P S : ι → Finset ℕ) {x : ℕ → ℝ} {a A : ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (ha : 0 < a) (hA : 0 ≤ A)
    (hsep : ∀ e ∈ H.edges, ∀ i ∈ I, ∀ j ∈ I,
      ¬ Disjoint (H.edge e) (P i) → ¬ Disjoint (H.edge e) (P j) → i = j)
    (hcost : ∀ i ∈ I, H.setCoverCost (S i) ≤
      A * a⁻¹ * H.coverCost (restrictDemand x (P i))) :
    H.setCoverCost (H.roundingThreshold x a ∪ I.biUnion S) ≤
      (A + 1) * a⁻¹ * H.coverCost x := by
  have hp := H.sum_restrictDemand_cost_le I P x hsep
  have hs : (∑ i ∈ I, H.setCoverCost (S i)) ≤ A * a⁻¹ * H.coverCost x := by
    calc
      _ ≤ ∑ i ∈ I, A * a⁻¹ * H.coverCost (restrictDemand x (P i)) :=
        sum_le_sum hcost
      _ = A * a⁻¹ * ∑ i ∈ I, H.coverCost (restrictDemand x (P i)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hA (inv_nonneg.mpr ha.le))
  calc
    _ ≤ H.setCoverCost (H.roundingThreshold x a) + H.setCoverCost (I.biUnion S) :=
      H.setCoverCost_union_le _ _
    _ ≤ a⁻¹ * H.coverCost x + A * a⁻¹ * H.coverCost x :=
      add_le_add (H.roundingThreshold_cost_le hx ha) ((H.setCoverCost_biUnion_le I S).trans hs)
    _ = _ := by ring
end Paper.Hypergraph
