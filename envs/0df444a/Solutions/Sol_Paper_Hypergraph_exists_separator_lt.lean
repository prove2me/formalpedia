-- Prove2me | solution 1 for Paper.Hypergraph.exists_separator_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:48.1128+00:00
-- url     : https://prove2.me/submissions/127527fd-ced9-4a62-937c-ce2240253380

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_cover_restriction
import Theorems.Thm_Paper_Hypergraph_full_integral_separator
import Theorems.Thm_Paper_Hypergraph_integralOptimum_bounds

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {W : Finset ℕ} (hW : W ⊆ H.vertices)
    {γ : ℕ → ℝ} (hγ : (H.induce W).EdgeWeight γ) {η r : ℝ}
    (hη : 0 < η ∧ η < 1) (hr : H.sep η < r) :
    ∃ S, (H.induce W).IntegralBalanced γ η S ∧ H.setCoverCost S < r := by
  have hb : BddAbove (insert 0 {r | ∃ W ⊆ H.vertices, ∃ γ,
      (H.induce W).EdgeWeight γ ∧ r = (H.induce W).integralOptimum η γ}) := by
    refine ⟨H.edges.card, ?_⟩
    rintro r (rfl | ⟨U, hU, δ, hδ, rfl⟩)
    · positivity
    · exact ((H.induce U).integralOptimum_bounds δ hδ hη).2.trans (by
        exact_mod_cast card_filter_le H.edges (fun e => (H.edge e ∩ U).Nonempty))
  have hh : (H.induce W).integralOptimum η γ < r :=
    (le_csSup hb (Set.mem_insert_of_mem 0 ⟨W, hW, γ, hγ, rfl⟩)).trans_lt hr
  obtain ⟨_, ⟨S, hS, rfl⟩, hc⟩ := exists_lt_of_csInf_lt
    (show {r | ∃ S, (H.induce W).IntegralBalanced γ η S ∧
      r = (H.induce W).setCoverCost S}.Nonempty from
      ⟨_, (H.induce W).vertices, (H.induce W).full_integral_separator γ η, rfl⟩) hh
  refine ⟨S, hS, ?_⟩
  rwa [H.cover_restriction (fun v hv => (mem_inter.mp (hS.1 hv)).2)] at hc
end Paper.Hypergraph
