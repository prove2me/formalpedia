-- Prove2me | solution 1 for Paper.Hypergraph.rounding_volume_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:08.888622+00:00
-- url     : https://prove2.me/submissions/55a0bd2a-4b82-4b9c-acf0-fc9f0c41fd56

import Definitions.Def_Paper_RoundingRecursion
import Definitions.Def_Paper_TwoTerminalRounding
import Definitions.Def_Paper_BalancedRounding

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {φ : ℝ} (hφ : 0 < φ ∧ φ < 1) :
    φ / (1 - (1 - φ) / 2) ≤ (1 + 3 * φ) / (2 + 2 * φ) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith [mul_nonneg (show 0 ≤ 1 - φ by linarith) (show 0 ≤ 1 + φ by linarith)]
end Paper.Hypergraph
