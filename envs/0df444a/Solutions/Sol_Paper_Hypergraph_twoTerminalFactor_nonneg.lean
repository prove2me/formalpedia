-- Prove2me | solution 1 for Paper.Hypergraph.twoTerminalFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:45.177947+00:00
-- url     : https://prove2.me/submissions/74502a42-1ed7-42f4-829d-62dda96554af

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
import Theorems.Thm_Paper_Hypergraph_log_nat_nonneg

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (R : Finset ℕ) : 0 ≤ H.twoTerminalFactor R := by
  apply le_min
  · have := log_nat_nonneg (H.induce R).independenceNumber
    linarith
  · positivity
end Paper.Hypergraph
