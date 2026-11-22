-- Prove2me | solution 1 for Paper.Hypergraph.cover_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:48.416136+00:00
-- url     : https://prove2.me/submissions/040d5d7d-6c02-46d8-9efd-6d0ed15dd6ad

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x y : ℕ → ℝ} (hy : H.Cover x y)
    {c : ℝ} (hc : 0 ≤ c) : H.Cover (c • x) (c • y) := by
  refine ⟨fun e he => mul_nonneg hc (hy.1 e he), ?_⟩
  intro v hv
  simpa [Pi.smul_apply, smul_eq_mul, mul_sum] using
    mul_le_mul_of_nonneg_left (hy.2 v hv) hc
end Paper.Hypergraph
