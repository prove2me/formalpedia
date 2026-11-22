-- Prove2me | solution 1 for Paper.Hypergraph.levelSeparator_subset_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:48.8058+00:00
-- url     : https://prove2.me/submissions/df86c869-a514-43c2-af23-8f3a3db2219a

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (x d : ℕ → ℝ) (r : ℝ) :
    H.levelSeparator x d r ⊆ H.vertices.filter (fun v => x v ≠ 0) := by
  intro v hv
  exact mem_filter.mpr ⟨(mem_filter.mp hv).1, (mem_filter.mp hv).2.1⟩
end Paper.Hypergraph
