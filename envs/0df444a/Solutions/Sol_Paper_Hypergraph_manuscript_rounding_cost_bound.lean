-- Prove2me | solution 1 for Paper.Hypergraph.manuscript_rounding_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:11.783826+00:00
-- url     : https://prove2.me/submissions/3392d0d2-300e-43d7-add8-856517fa8966

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
import Definitions.Def_Paper_RoundingComplete

set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {q : ℝ} (hq : 0 ≤ q) :
    ((44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ))) * q ≤
      120 * q * (Real.log (max 2 q) / Real.log 2) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let L := Real.log (max 2 q) / Real.log 2
  have hL : 1 ≤ L := by
    apply (le_div_iff₀ h2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (le_max_left 2 q)
  have hlog : Real.log (q / (1 - (1 / 2 : ℝ))) ≤
      Real.log 2 + Real.log (max 2 q) := by
    calc
      _ ≤ Real.log (2 * max 2 q) := by
        apply Real.log_le_log (by positivity)
        have := le_max_right (2 : ℝ) q
        norm_num
        linarith
      _ = _ := Real.log_mul (by norm_num) (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left 2 q)))
  have hratio : Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2 ≤ 1 + L := by
    apply (div_le_iff₀ h2).mpr
    calc
      _ ≤ Real.log 2 + Real.log (max 2 q) := hlog
      _ = (1 + L) * Real.log 2 := by dsimp [L]; field_simp
  have hfactor : (44 + 8 * (Real.log (q / (1 - (1 / 2 : ℝ))) / Real.log 2)) /
      (1 - (1 / 2 : ℝ)) ≤ 120 * L := by
    norm_num at hratio ⊢
    linarith
  calc
    _ ≤ (120 * L) * q := mul_le_mul_of_nonneg_right hfactor hq
    _ = _ := by dsimp [L]; ring
end Paper.Hypergraph
