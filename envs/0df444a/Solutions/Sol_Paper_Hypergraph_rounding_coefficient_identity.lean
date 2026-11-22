-- Prove2me | solution 1 for Paper.Hypergraph.rounding_coefficient_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:06.633781+00:00
-- url     : https://prove2.me/submissions/f6569040-3e64-4631-bfb2-0262e331b84e

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
theorem _root_.solution {K φ : ℝ} (hK : 0 < K) (hφ : φ < 1) :
    (18 + 4 * Real.logb 2 (K / ((1 - φ) / 2))) / ((1 - φ) / 2) =
      (44 + 8 * (Real.log (K / (1 - φ)) / Real.log 2)) / (1 - φ) := by
  have hden : 1 - φ ≠ 0 := ne_of_gt (sub_pos.mpr hφ)
  have harg : K / ((1 - φ) / 2) = 2 * (K / (1 - φ)) := by field_simp
  rw [harg, Real.logb_mul (by norm_num) (div_ne_zero hK.ne' hden),
    Real.logb_self_eq_one (by norm_num)]
  simp only [Real.logb]
  field_simp
  ring
end Paper.Hypergraph
