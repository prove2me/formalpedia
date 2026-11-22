-- Prove2me | solution 1 for Paper.Hypergraph.roundingBall_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:40.0322+00:00
-- url     : https://prove2.me/submissions/d12aa8c4-6688-40ec-ab1e-16db1e73112d

import Definitions.Def_Paper_RoundingGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_Paper_RoundingPaths

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x : ℕ → ℝ) (Q : Finset ℕ) (c : ℕ)
    {a b : ℝ} (hab : a ≤ b) : H.roundingBall x Q c a ⊆ H.roundingBall x Q c b := by
  intro v hv
  exact mem_filter.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hv).2.trans hab⟩
end Paper.Hypergraph
