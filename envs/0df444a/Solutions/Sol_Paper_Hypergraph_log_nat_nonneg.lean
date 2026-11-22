-- Prove2me | solution 1 for Paper.Hypergraph.log_nat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:35.596048+00:00
-- url     : https://prove2.me/submissions/c8047692-d15c-4eb7-8719-4d321e912791

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
end Paper.Hypergraph
