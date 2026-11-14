-- Prove2me | solution 1 for TaoFivePrimes.dusart_table1_psi_bounds_below_300_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-13T21:53:08.915544+00:00
-- url     : https://prove2.me/submissions/cb3e839c-6ad4-4781-96e1-9206abae18b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bound_row_23_20261114
import Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_below_300_except_23_20261114
set_option autoImplicit false
noncomputable section

theorem solution (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
 (hb : r.b < 300) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) :
 |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ)*x := by
 let h23 := TaoFivePrimes.dusart_table1_psi_bound_row_23_20261114
 let hother := TaoFivePrimes.dusart_table1_psi_bounds_below_300_except_23_20261114
 by_cases h : r.b = 23
 · have hrow : r = ⟨23,24,2431/10^7⟩ := by
     simp only [DusartThetaTable.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
     rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
     all_goals norm_num at h <;> norm_num
   subst r
   convert h23 x (by simpa using hx) using 1 <;> norm_num
 · exact hother r hr hb h x hx
