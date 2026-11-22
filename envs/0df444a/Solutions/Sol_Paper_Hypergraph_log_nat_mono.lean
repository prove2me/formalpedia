-- Prove2me | solution 1 for Paper.Hypergraph.log_nat_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:07.466802+00:00
-- url     : https://prove2.me/submissions/2da7287f-2ccc-4921-bc1e-638f0e946996

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
theorem _root_.solution {m n : ℕ} (hmn : m ≤ n) : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  by_cases hm : m = 0
  · simpa [hm] using log_nat_nonneg n
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm) (by exact_mod_cast hmn)
end Paper.Hypergraph
