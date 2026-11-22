-- Prove2me | solution 1 for Paper.Hypergraph.coverCost_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:34.011171+00:00
-- url     : https://prove2.me/submissions/ba69e751-f995-4c48-8684-bf399fb0337b

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_le_coverCost
import Theorems.Thm_Paper_Hypergraph_cover_smul

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    H.coverCost (c • x) ≤ c * H.coverCost x := by
  rw [mul_comm c, ← div_le_iff₀ hc]
  apply H.le_coverCost
  intro y hy
  rw [div_le_iff₀ hc]
  simpa [Pi.smul_apply, smul_eq_mul, mul_sum, mul_comm] using
    H.coverCost_le (H.cover_smul hy hc.le)
end Paper.Hypergraph
