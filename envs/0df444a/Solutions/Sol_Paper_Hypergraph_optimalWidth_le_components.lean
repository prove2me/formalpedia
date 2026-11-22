-- Prove2me | solution 1 for Paper.Hypergraph.optimalWidth_le_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:17.044553+00:00
-- url     : https://prove2.me/submissions/6b4f0780-030d-46b9-9934-40437891dd7a

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_optimalWidth_le_bagWidth
import Theorems.Thm_Paper_Hypergraph_glue_component_decompositions

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (b : Finset ℕ → ℝ) (r : ℝ)
    (hb : ∀ S ⊆ H.vertices, 0 ≤ b S) (hzero : b ∅ ≤ r)
    (hcomp : ∀ C ∈ H.components, (H.induce C).optimalWidth b ≤ r) :
    H.optimalWidth b ≤ r := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro s hrs
  have hlocal : ∀ C ∈ H.components, ∃ n, ∃ D : (H.induce C).TreeDecomposition n,
      ∀ t, b (D.bag t) ≤ s := by
    intro C hC
    have hlo : (H.induce C).optimalWidth b < s := (hcomp C hC).trans_lt hrs
    obtain ⟨r', ⟨n, D, rfl⟩, hD⟩ := exists_lt_of_csInf_lt
      (show {r | ∃ n, ∃ D : (H.induce C).TreeDecomposition n, r = D.bagWidth b}.Nonempty
        from ⟨_, 0, (H.induce C).oneBag, rfl⟩) hlo
    refine ⟨n, D, fun t => ?_⟩
    exact (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩).trans hD.le
  obtain ⟨n, D, hD⟩ := H.glue_component_decompositions b s (hzero.trans hrs.le) hlocal
  apply (H.optimalWidth_le_bagWidth b hb D).trans
  refine csSup_le ⟨_, 0, rfl⟩ ?_
  rintro r ⟨t, rfl⟩
  exact hD t
end Paper.Hypergraph
