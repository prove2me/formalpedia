-- Prove2me | solution 1 for SoficGroups.SourceCompressionMatching.lt_exp_mul_of_equal_log_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/ee705d74-c0f5-4d5a-b1e5-c2c3bab32d0d

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionMatching
theorem _root_.solution
    {x y H r : ℝ} (hx : 0 < x) (hy : 0 < y) (hH : 0 < H)
    (hrank :
      ⌊(Real.log x + r) / H⌋ = ⌊(Real.log y + r) / H⌋) :
    y < Real.exp H * x := by
  have hyfloor := Int.lt_floor_add_one ((Real.log y + r) / H)
  rw [← hrank] at hyfloor
  have hxloor := Int.floor_le ((Real.log x + r) / H)
  have hratio :
      (Real.log y + r) / H < (Real.log x + r) / H + 1 :=
    hyfloor.trans_le (by
      simpa [add_comm] using (add_le_add_right hxloor 1))
  have hscaled := mul_lt_mul_of_pos_right hratio hH
  have hcancel :
      ((Real.log x + r) / H + 1) * H =
        Real.log x + r + H := by
    rw [add_mul, div_mul_cancel₀ _ hH.ne', one_mul]
  have hlog : Real.log y < Real.log x + H := by
    rw [div_mul_cancel₀ _ hH.ne', hcancel] at hscaled
    linarith
  have hexp := (Real.exp_lt_exp).2 hlog
  rw [Real.exp_log hy, Real.exp_add, Real.exp_log hx] at hexp
  simpa [mul_comm] using hexp
end SoficGroups.SourceCompressionMatching
