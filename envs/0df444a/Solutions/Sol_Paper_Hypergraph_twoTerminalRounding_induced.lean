-- Prove2me | solution 1 for Paper.Hypergraph.twoTerminalRounding_induced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:29.307494+00:00
-- url     : https://prove2.me/submissions/9bdb350e-0206-4b3f-a807-c6d0f94cc243

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
import Theorems.Thm_Paper_Hypergraph_twoTerminalFactor_induce_le
import Theorems.Thm_Paper_Hypergraph_cover_restriction


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (round : TwoTerminalRounding) (H : Hypergraph)
    (Q : Finset ℕ) (x : ℕ → ℝ) (A B : Finset ℕ) (z : ℕ → ℝ)
    (hA : A ⊆ (H.induce Q).vertices) (hB : B ⊆ (H.induce Q).vertices)
    (hz : (H.induce Q).FractionalSeparator A B z)
    (hsupp : ∀ v ∈ (H.induce Q).vertices, z v ≠ 0 → x v ≠ 0) :
    ∃ S ⊆ (H.induce Q).vertices.filter (fun v => z v ≠ 0),
      (H.induce Q).IntegralSeparator A B S ∧
      H.setCoverCost S ≤ H.twoTerminalFactor (H.vertices.filter (fun v => x v ≠ 0)) *
        (H.induce Q).coverCost z := by
  obtain ⟨S, hS, hsep, hcost⟩ := round (H.induce Q) A B z hA hB hz
  have hSQ : S ⊆ Q := fun v hv => (mem_inter.mp (mem_filter.mp (hS hv)).1).2
  have hs : (H.induce Q).vertices.filter (fun v => z v ≠ 0) ⊆
      H.vertices.filter (fun v => x v ≠ 0) := by
    intro v hv
    obtain ⟨hv, hzv⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨(mem_inter.mp hv).1, hsupp v hv hzv⟩
  refine ⟨S, hS, hsep, ?_⟩
  rw [H.cover_restriction hSQ] at hcost
  exact hcost.trans (mul_le_mul_of_nonneg_right (H.twoTerminalFactor_induce_le Q hs)
    ((H.induce Q).coverCost_nonneg z))
end Paper.Hypergraph
