-- Prove2me | solution 2 for TaoFivePrimes.schoenfeld_psi_error_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T16:19:23.823243+00:00
-- url     : https://prove2.me/submissions/ad037853-cb76-4469-97d2-a8738f28390e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_to_exp23
import Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_for_log_four
import Theorems.Thm_ExplicitPNT_dusart_table1_psi_power_error

set_option maxHeartbeats 1000000

theorem solution (y : ℝ) (hy : 10 ^ 8 ≤ y) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  have hypos : 0 < y := by linarith
  have htpos : 0 < Real.log y := Real.log_pos (by linarith)
  by_cases hsmall : y < Real.exp 23
  · exact TaoFivePrimes.schoenfeld_psi_error_to_exp23 y hy hsmall
  have ht23 : (23 : ℝ) ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos 23) (le_of_not_gt hsmall)
    simpa using this
  by_cases hlarge : 300 ≤ Real.log y
  · let t := Real.log y
    have ht : 300 ≤ t := hlarge
    have hpsi := ExplicitPNT.dusart_table1_psi_power_error t ht
    have hexp : Real.exp t = y := Real.exp_log hypos
    have hpow : (1048576 : ℝ) ≤ Real.exp 20 := by
      have hbase : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase 20
      norm_num at hp ⊢
      simpa [Real.exp_nat_mul] using hp
    have h20 : (20 : ℝ) ≤ 2 * t / 30 := by linarith
    have hA : t / 30 ≤ Real.exp (t / 30) := by linarith [Real.add_one_le_exp (t / 30)]
    have hB : (1048576 : ℝ) ≤ Real.exp (2 * t / 30) := hpow.trans (Real.exp_le_exp.mpr h20)
    have hm : 5600 * t ≤ Real.exp (t / 10) := by
      have hp := mul_le_mul hA hB (by norm_num : (0:ℝ) ≤ 1048576) (Real.exp_nonneg (t/30))
      have he : Real.exp (t / 30) * Real.exp (2*t/30) = Real.exp (t/10) := by
        rw [← Real.exp_add]; congr 1 <;> ring
      rw [he] at hp
      nlinarith
    have hbound : 140 * Real.exp (9*t/10) ≤ Real.exp t / (40*t) := by
      have ht0 : 0 < 40*t := by linarith
      apply (le_div_iff₀ ht0).2
      have hm' := mul_le_mul_of_nonneg_left hm (Real.exp_nonneg (9*t/10))
      have he : Real.exp (9*t/10) * Real.exp (t/10) = Real.exp t := by
        rw [← Real.exp_add]; congr 1 <;> ring
      rw [he] at hm'
      nlinarith
    simpa [t, hexp] using hpsi.trans hbound
  · have ht300 : Real.log y < 300 := lt_of_not_ge hlarge
    by_cases h100 : Real.log y < 100
    · let r : DusartThetaTable.Row := ⟨23,24,2431/10^7⟩
      have hr : r ∈ DusartThetaTable.rows := by norm_num [r, DusartThetaTable.rows]
      have hx : Real.exp (r.b : ℝ) ≤ y := by
        change Real.exp 23 ≤ y
        calc
          Real.exp 23 ≤ Real.exp (Real.log y) := Real.exp_le_exp.mpr ht23
          _ = y := Real.exp_log hypos
      have hp := TaoFivePrimes.dusart_table1_psi_bounds_for_log_four r hr y hx
      have hc : (2431 / 10^7 : ℝ) * y ≤ y / (40 * Real.log y) := by
        apply (le_div_iff₀ (by positivity : 0 < 40 * Real.log y)).2
        nlinarith
      exact hp.trans (by simpa [r] using hc)
    · let r : DusartThetaTable.Row := ⟨100,200,1815/10^14⟩
      have hr : r ∈ DusartThetaTable.rows := by norm_num [r, DusartThetaTable.rows]
      have hx : Real.exp (r.b : ℝ) ≤ y := by
        change Real.exp 100 ≤ y
        calc
          Real.exp 100 ≤ Real.exp (Real.log y) := Real.exp_le_exp.mpr (le_of_not_gt h100)
          _ = y := Real.exp_log hypos
      have hp := TaoFivePrimes.dusart_table1_psi_bounds_for_log_four r hr y hx
      have hc : (1815 / 10^14 : ℝ) * y ≤ y / (40 * Real.log y) := by
        apply (le_div_iff₀ (by positivity : 0 < 40 * Real.log y)).2
        nlinarith
      exact hp.trans (by simpa [r] using hc)
