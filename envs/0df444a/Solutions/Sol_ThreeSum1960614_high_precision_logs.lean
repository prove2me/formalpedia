-- Prove2me | solution 1 for ThreeSum1960614.high_precision_logs
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:14:54.929978+00:00
-- url     : https://prove2.me/submissions/c980546c-efb4-4e0e-b983-36cd843fbc70

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open scoped BigOperators
open ThreeSum1960614

private noncomputable def logSeries (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * i + 1)

private theorem log_interval {y z L U : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hy : (1 + z) / (1 - z) = y) (n : ℕ)
    (hlo : L ≤ 2 * logSeries n z)
    (hhi : 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) ≤ U) :
    L ≤ Real.log y ∧ Real.log y ≤ U := by
  have hl := mul_le_mul_of_nonneg_left (Real.sum_range_le_log_div hz0 hz1 n)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hu := mul_le_mul_of_nonneg_left (Real.log_div_le_sum_range_add hz0 hz1 n)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hleft : 2 * logSeries n z ≤ Real.log y := by
    rw [← hy]
    simpa [logSeries, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hl
  have hright : Real.log y ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
    rw [← hy]
    calc
      Real.log ((1 + z) / (1 - z)) = 2 * (1 / 2 * Real.log ((1 + z) / (1 - z))) := by ring
      _ ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
        simpa [logSeries] using hu
  exact ⟨hlo.trans hleft, hright.trans hhi⟩

theorem solution :
    ((6931471805599453094172 / 10 ^ 22 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 6931471805599453094173 / 10 ^ 22) ∧
    ((5947071077466927895143 / 10 ^ 22 : ℝ) ≤ Real.log (29 / 16) ∧
      Real.log (29 / 16) ≤ 5947071077466927895144 / 10 ^ 22) ∧
    ((43196611445164148724 / 10 ^ 22 : ℝ) ≤ Real.log (232 / 231) ∧
      Real.log (232 / 231) ≤ 43196611445164148725 / 10 ^ 22) ∧
    ((21574981400211907723 / 10 ^ 22 : ℝ) ≤ Real.log (464 / 463) ∧
      Real.log (464 / 463) ≤ 21574981400211907724 / 10 ^ 22) ∧
    ((2570554035235070921259 / 10 ^ 22 : ℝ) ≤ Real.log (32 * theta) ∧
      Real.log (32 * theta) ≤ 2570554035235070921260 / 10 ^ 22) ∧
    ((6518981167335747474116 / 10 ^ 22 : ℝ) ≤ Real.log (2 * (1 - theta)) ∧
      Real.log (2 * (1 - theta)) ≤ 6518981167335747474117 / 10 ^ 22) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact log_interval (z := (1 : ℝ) / 3) (by norm_num) (by norm_num)
      (by norm_num) 26 (by norm_num [logSeries]) (by norm_num [logSeries])
  · exact log_interval (z := (13 : ℝ) / 45) (by norm_num) (by norm_num)
      (by norm_num) 24 (by norm_num [logSeries]) (by norm_num [logSeries])
  · exact log_interval (z := (1 : ℝ) / 463) (by norm_num) (by norm_num)
      (by norm_num) 5 (by norm_num [logSeries]) (by norm_num [logSeries])
  · exact log_interval (z := (1 : ℝ) / 927) (by norm_num) (by norm_num)
      (by norm_num) 5 (by norm_num [logSeries]) (by norm_num [logSeries])
  · exact log_interval (z := (9159899 : ℝ) / 71659899) (by norm_num) (by norm_num)
      (by norm_num [theta]) 18 (by norm_num [logSeries]) (by norm_num [logSeries])
  · exact log_interval (z := (459590101 : ℝ) / 1459590101) (by norm_num) (by norm_num)
      (by norm_num [theta]) 26 (by norm_num [logSeries]) (by norm_num [logSeries])

#print axioms solution
