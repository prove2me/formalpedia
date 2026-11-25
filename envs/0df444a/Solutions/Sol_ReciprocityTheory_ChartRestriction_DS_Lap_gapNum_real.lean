-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.gapNum_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:56.929141+00:00
-- url     : https://prove2.me/submissions/110d4a59-f318-485a-951e-36d91a38d514

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_GapNum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_gapNum_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution (Q Nn T P Q0 x : ℝ) (hQ : 1 ≤ Q) (hN : 2 ≤ Nn) (hT : Nn + 5 ≤ T)
    (hP : P ≤ Nn) (hQ00 : 0 ≤ Q0) (hQ0 : Q0 ≤ Q)
    (hx : 2 * (Nn + 2 * Q * T) ^ 3 + T + 3 < x) :
    max (2 + max (3 * Nn / 2) (1 + Nn * P * Q))
      (max (16 * Nn * Q0 + 8 * Real.sqrt (2 * Q0) + 2)
        (8 * Real.sqrt (2 * Q0) * (4 * max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) + 1))) < x := by
  have key := gapNum_key Q Nn T hQ hN hT
  have hQp : 0 ≤ Q := by linarith
  have hNp : 0 ≤ Nn := by linarith
  have hTp : 0 ≤ T := by linarith
  set S := Nn + 2 * Q * T with hS
  have hSN : Nn ≤ S := by nlinarith
  have hS3 : Nn ≤ 2 * S ^ 3 := by nlinarith [sq_nonneg S, sq_nonneg Nn]
  have hs0 : 0 ≤ Real.sqrt (2 * Q0) := Real.sqrt_nonneg _
  have hs : Real.sqrt (2 * Q0) ≤ 2 * Q := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hm0 : 0 ≤ max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) :=
    le_max_of_le_left (by positivity)
  have hm : max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) ≤ 2 * Q * Nn ^ 2 :=
    max_le (by nlinarith [mul_le_mul_of_nonneg_left hQ0 hNp, mul_le_mul_of_nonneg_left (show Nn ≤ Nn ^ 2 by nlinarith) (show 0 ≤ Q by linarith)]) (by nlinarith)
  have hN2 : 4 ≤ Nn ^ 2 := by nlinarith
  have hQN : 4 * Q ≤ Q ^ 2 * Nn ^ 2 := by
    calc 4 * Q ≤ Q ^ 2 * 4 := by nlinarith
      _ ≤ Q ^ 2 * Nn ^ 2 := mul_le_mul_of_nonneg_left hN2 (sq_nonneg Q)
  have hd : 8 * Real.sqrt (2 * Q0) * (4 * max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) + 1)
      ≤ 8 * (2 * Q) * (4 * (2 * Q * Nn ^ 2) + 1) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hNQ : Nn * Q0 ≤ Nn * Q := mul_le_mul_of_nonneg_left hQ0 hNp
  have hqn : 2 ≤ Q * Nn := by nlinarith
  have hQ2N2 : 2 * (Nn * Q) ≤ Q ^ 2 * Nn ^ 2 := by nlinarith
  have hPQ : P * Q ≤ Nn * Q := mul_le_mul_of_nonneg_right hP hQp
  have hNPQ1 : Nn * (P * Q) ≤ Nn * (Nn * Q) := mul_le_mul_of_nonneg_left hPQ hNp
  have hQQ : Q ≤ Q ^ 2 := by nlinarith
  have hNPQ2 : Nn ^ 2 * Q ≤ Nn ^ 2 * Q ^ 2 := mul_le_mul_of_nonneg_left hQQ (sq_nonneg Nn)
  have hQN0 : 0 ≤ Q ^ 2 * Nn ^ 2 := by positivity
  refine max_lt ?_ (max_lt ?_ ?_)
  · have : max (3 * Nn / 2) (1 + Nn * P * Q) < x - 2 :=
      max_lt (by linarith) (by nlinarith)
    linarith
  · nlinarith
  · nlinarith
end ReciprocityTheory.ChartRestriction.DS.Lap
