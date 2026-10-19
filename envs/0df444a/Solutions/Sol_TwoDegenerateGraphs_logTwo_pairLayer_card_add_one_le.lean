-- Prove2me | solution 1 for TwoDegenerateGraphs.logTwo_pairLayer_card_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/55b34919-41bf-4613-8495-5fadace7b995

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (L : ℕ) (hL : 2 ≤ L) :
    logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
      2 * (L : ℝ) / Real.log 2 := by
  let x : ℝ := ((L.choose 2 + 1 : ℕ) : ℝ)
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hLreal : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 := by
    exact Nat.cast_choose_two ℝ L
  have hxle : x ≤ (L : ℝ) ^ 2 := by
    dsimp [x]
    push_cast
    rw [hchoose]
    nlinarith [sq_nonneg ((L : ℝ) - 1)]
  have hsqrt : Real.sqrt x ≤ (L : ℝ) := by
    have hsq := Real.sq_sqrt hxpos.le
    have hsqrt_nonneg := Real.sqrt_nonneg x
    nlinarith
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have hbound := Real.log_le_rpow_div hxpos.le
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hbound
    norm_num at hbound
    linarith
  change Real.log x / Real.log 2 ≤ 2 * (L : ℝ) / Real.log 2
  apply (div_le_div_iff_of_pos_right log_two_pos).mpr
  linarith
end TwoDegenerateGraphs
