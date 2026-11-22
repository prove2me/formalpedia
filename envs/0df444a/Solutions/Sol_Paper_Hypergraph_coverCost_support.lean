-- Prove2me | solution 1 for Paper.Hypergraph.coverCost_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:33.717271+00:00
-- url     : https://prove2.me/submissions/e405d47c-1c0b-44b7-be49-9144307bfa83

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_coverCost_add_le
import Theorems.Thm_Paper_Hypergraph_coverCost_smul

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ) :
    ∃ g : (ℕ → ℝ) →ₗ[ℝ] ℝ, g x = H.coverCost x ∧ ∀ z, g z ≤ H.coverCost z := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, ?_, fun z => H.coverCost_nonneg z⟩
    simp [H.coverCost_eq_zero_of_nonpos (x := 0) (by simp)]
  let f : (ℕ → ℝ) →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton x (H.coverCost x) hx
  have hf : ∀ z : f.domain, f z ≤ H.coverCost z := by
    rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [f, LinearPMap.mkSpanSingleton, LinearPMap.mkSpanSingleton'_apply,
      RingHom.id_apply, smul_eq_mul]
    by_cases hc : 0 < c
    · exact (H.coverCost_smul x hc).ge
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc)
        (H.coverCost_nonneg x)).trans (H.coverCost_nonneg _)
  obtain ⟨g, hg, hbound⟩ := exists_extension_of_le_sublinear f H.coverCost
    (fun c hc z => H.coverCost_smul z hc) H.coverCost_add_le hf
  refine ⟨g, ?_, hbound⟩
  exact (hg ⟨x, Submodule.mem_span_singleton_self x⟩).trans
    (LinearPMap.mkSpanSingleton_apply ℝ ℝ hx _)
end Paper.Hypergraph
