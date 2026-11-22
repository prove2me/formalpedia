-- Prove2me | solution 1 for Paper.Hypergraph.cover_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:38.166311+00:00
-- url     : https://prove2.me/submissions/cdf2ec77-4607-4c22-8307-9710c3c1ae4d

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
theorem _root_.solution (H : Hypergraph) {x z y u : ℕ → ℝ}
    (hy : H.Cover x y) (hu : H.Cover z u) : H.Cover (x + z) (y + u) := by
  refine ⟨fun e he => add_nonneg (hy.1 e he) (hu.1 e he), ?_⟩
  intro v hv
  simpa [Pi.add_apply, sum_add_distrib] using add_le_add (hy.2 v hv) (hu.2 v hv)
end Paper.Hypergraph
