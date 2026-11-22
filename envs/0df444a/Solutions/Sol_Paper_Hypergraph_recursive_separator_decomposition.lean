-- Prove2me | solution 1 for Paper.Hypergraph.recursive_separator_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:28.631101+00:00
-- url     : https://prove2.me/submissions/85ed4af2-d611-4887-99b7-48c56b83be5f

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_optimalWidth_le_bagWidth
import Theorems.Thm_Paper_Hypergraph_sep_bounds
import Theorems.Thm_Paper_Hypergraph_recursive_rooted_decomposition

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {η : ℝ}
    (hη : 0 < η ∧ η < 1) :
    H.fhw ≤ (2 - η) / (1 - η) * (H.sep η + 1) := by
  have hden : 0 < 1 - η := sub_pos.mpr hη.2
  let a := (2 - η) / (1 - η)
  have ha : 0 < a := div_pos (by linarith) hden
  have happrox (r : ℝ) (hr : H.sep η < r) : H.fhw ≤ a * (r + 1) := by
    have hr0 : 0 ≤ r := (H.sep_bounds hη).1.trans hr.le
    obtain ⟨n,D,root,hroot,hD⟩ := H.recursive_rooted_decomposition hη hr H.vertices ∅
      (Subset.refl _) (empty_subset _) (by
        rw [H.setCoverCost_empty]
        exact div_nonneg (by linarith) hden.le)
    have hw : H.fhw ≤ (r + 1) / (1 - η) + r + 1 := by
      apply (H.optimalWidth_le_bagWidth H.setCoverCost
        (fun S _ => H.coverCost_nonneg (indicator S)) D.ofInduceVertices).trans
      refine csSup_le ⟨_,0,rfl⟩ ?_
      rintro s ⟨t,rfl⟩
      exact hD t
    convert hw using 1
    dsimp [a]
    field_simp [ne_of_gt hden]
    ring
  have hlim : H.fhw / a - 1 ≤ H.sep η := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    have hh : H.fhw / a ≤ r + 1 := (div_le_iff₀ ha).mpr (by
      simpa only [mul_comm] using happrox r hr)
    linarith
  have hh := (div_le_iff₀ ha).mp (show H.fhw / a ≤ H.sep η + 1 by linarith)
  simpa only [mul_comm] using hh
end Paper.Hypergraph
