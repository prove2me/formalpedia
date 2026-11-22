-- Prove2me | solution 1 for Paper.Hypergraph.beta_le_adw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:36.263072+00:00
-- url     : https://prove2.me/submissions/2df5d6f2-484d-4dde-a141-78c617e793e9

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_optimal_modular_le_adw
import Theorems.Thm_Paper_Hypergraph_indicator_equivalence
import Theorems.Thm_Paper_Hypergraph_balanced_bag
import Theorems.Thm_Paper_Hypergraph_fractional_cover_minimax

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ : ℕ → ℝ} (hγ : H.EdgeWeight γ)
    {θ : ℝ} (hθ : 1 / 2 ≤ θ ∧ θ < 1) : H.beta θ γ ≤ H.adw := by
  have hθ' : 0 < θ ∧ θ < 1 := ⟨by linarith [hθ.1], hθ.2⟩
  obtain ⟨w, hw, hminimax⟩ := H.fractional_cover_minimax hγ hθ'
  apply le_trans ?_ (H.optimal_modular_le_adw hw)
  refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
  rintro r ⟨n, D, rfl⟩
  obtain ⟨t, ht⟩ := H.balanced_bag hγ D
  have htθ : H.IntegralBalanced γ θ (D.bag t) := by
    refine ⟨ht.1, ?_⟩
    intro K hK
    exact (ht.2 K hK).trans (mul_le_mul_of_nonneg_right hθ.1 hγ.2.le)
  have hfrac := (H.indicator_equivalence hγ hθ' (D.bag_subset t)).mpr htθ
  have hdot := hminimax (indicator (D.bag t)) hfrac
  have hsum : (∑ v ∈ H.vertices, w v * indicator (D.bag t) v) =
      modularValue w (D.bag t) := by
    simp only [indicator, mul_ite, mul_one, mul_zero, ← sum_filter, modularValue]
    congr 1
    ext v
    simp only [mem_filter]
    exact ⟨And.right, fun hv => ⟨D.bag_subset t hv, hv⟩⟩
  rw [hsum] at hdot
  exact hdot.trans (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)
end Paper.Hypergraph
