-- Prove2me | solution 1 for Paper.Hypergraph.separator_characterization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:06.662537+00:00
-- url     : https://prove2.me/submissions/a7f00a3f-1446-429b-8d9a-541749d6e25a

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_elementary_width_bounds
import Theorems.Thm_Paper_Hypergraph_width_hereditary
import Theorems.Thm_Paper_Hypergraph_balanced_bag
import Theorems.Thm_Paper_Hypergraph_recursive_separator_decomposition

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {η : ℝ}
    (hη : 1 / 2 ≤ η ∧ η < 1) :
    H.sep η ≤ H.fhw ∧ H.fhw ≤ (2 - η) / (1 - η) * (H.sep η + 1) := by
  refine ⟨?_, H.recursive_separator_decomposition ⟨by linarith [hη.1], hη.2⟩⟩
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro r (rfl | ⟨W, hW, γ, hγ, rfl⟩)
  · exact H.elementary_width_bounds.2.2
  · apply le_trans ?_ (H.width_hereditary W).2
    refine le_csInf ⟨_, 0, (H.induce W).oneBag, rfl⟩ ?_
    rintro r ⟨n, D, rfl⟩
    obtain ⟨t, ht⟩ := (H.induce W).balanced_bag hγ D
    have htη : (H.induce W).IntegralBalanced γ η (D.bag t) := by
      refine ⟨ht.1, ?_⟩
      intro K hK
      exact (ht.2 K hK).trans (mul_le_mul_of_nonneg_right hη.1 hγ.2.le)
    have hopt : (H.induce W).integralOptimum η γ ≤ (H.induce W).setCoverCost (D.bag t) := by
      refine csInf_le ⟨0, ?_⟩ ⟨D.bag t, htη, rfl⟩
      rintro r ⟨S, hS, rfl⟩
      exact (H.induce W).coverCost_nonneg (indicator S)
    exact hopt.trans (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)
end Paper.Hypergraph
