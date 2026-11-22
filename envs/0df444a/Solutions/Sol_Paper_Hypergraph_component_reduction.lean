-- Prove2me | solution 1 for Paper.Hypergraph.component_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:03.99261+00:00
-- url     : https://prove2.me/submissions/6fecd799-9056-489a-a33e-862d0ab01c73

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_cover_restriction
import Theorems.Thm_Paper_Hypergraph_elementary_width_bounds
import Theorems.Thm_Paper_Hypergraph_optimal_modular_le_adw
import Theorems.Thm_Paper_Hypergraph_width_hereditary
import Theorems.Thm_Paper_Hypergraph_optimalWidth_mono_cost
import Theorems.Thm_Paper_Hypergraph_optimalWidth_le_components

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) :
    H.fhw = sSup (insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).fhw}) ∧
    H.adw = sSup (insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).adw}) := by
  let F : Set ℝ := insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).fhw}
  let A : Set ℝ := insert 0 {r | ∃ C ∈ H.components, r = (H.induce C).adw}
  have hFbound : ∀ r ∈ F, r ≤ H.fhw := by
    rintro r (rfl | ⟨C, hC, rfl⟩)
    · exact H.elementary_width_bounds.2.2
    · exact (H.width_hereditary C).2
  have hAbound : ∀ r ∈ A, r ≤ H.adw := by
    rintro r (rfl | ⟨C, hC, rfl⟩)
    · exact H.elementary_width_bounds.1
    · exact (H.width_hereditary C).1
  have hF0 : 0 ≤ sSup F := le_csSup ⟨H.fhw, hFbound⟩ (Set.mem_insert 0 _)
  have hA0 : 0 ≤ sSup A := le_csSup ⟨H.adw, hAbound⟩ (Set.mem_insert 0 _)
  constructor
  · apply le_antisymm _ (csSup_le ⟨0, Set.mem_insert 0 _⟩ hFbound)
    apply H.optimalWidth_le_components H.setCoverCost (sSup F)
      (fun S _ => H.coverCost_nonneg (indicator S))
    · have hz : H.setCoverCost ∅ = 0 :=
        H.coverCost_eq_zero_of_nonpos (by simp [indicator])
      exact hz ▸ hF0
    · intro C hC
      have hm : (H.induce C).fhw ≤ sSup F :=
        le_csSup ⟨H.fhw, hFbound⟩ (Set.mem_insert_of_mem 0 ⟨C, hC, rfl⟩)
      apply le_trans _ hm
      apply (H.induce C).optimalWidth_mono_cost H.setCoverCost (H.induce C).setCoverCost
        (fun S _ => H.coverCost_nonneg (indicator S))
      intro S hS
      exact (H.cover_restriction (fun v hv => (mem_inter.mp (hS hv)).2)).ge
  · apply le_antisymm _ (csSup_le ⟨0, Set.mem_insert 0 _⟩ hAbound)
    have hz : H.ModularWeight (fun _ => 0) := ⟨by simp, by simp⟩
    refine csSup_le ⟨_, _, hz, rfl⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    apply H.optimalWidth_le_components (modularValue w) (sSup A)
      (fun S _ => sum_nonneg (fun v _ => hw.1 v))
      (by simpa [modularValue] using hA0)
    intro C hC
    have hwC : (H.induce C).ModularWeight w := by
      refine ⟨hw.1, ?_⟩
      intro e he
      exact (sum_le_sum_of_subset_of_nonneg inter_subset_left
        (fun v _ _ => hw.1 v)).trans (hw.2 e (mem_filter.mp he).1)
    exact ((H.induce C).optimal_modular_le_adw hwC).trans
      (le_csSup ⟨H.adw, hAbound⟩ (Set.mem_insert_of_mem 0 ⟨C, hC, rfl⟩))
end Paper.Hypergraph
