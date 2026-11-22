-- Prove2me | solution 1 for Paper.Hypergraph.coverCost_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:20.3359+00:00
-- url     : https://prove2.me/submissions/78f5958f-2df8-491e-bcba-6c8044eb5577

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_coverCost_smul_le

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    H.coverCost (c • x) = c * H.coverCost x := by
  apply le_antisymm (H.coverCost_smul_le x hc)
  have hi := H.coverCost_smul_le (c • x) (inv_pos.mpr hc)
  simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hi
  have := mul_le_mul_of_nonneg_left hi hc.le
  simpa [← mul_assoc, mul_inv_cancel₀ hc.ne'] using this
end Paper.Hypergraph
