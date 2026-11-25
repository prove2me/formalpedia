-- Prove2me | solution 1 for PI.PrimesDyadicRS.K.tstR_sound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:00.874248+00:00
-- url     : https://prove2.me/submissions/01697e04-b0ca-4fdc-b683-081cfe1d3abd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K
open Real
namespace PI.PrimesDyadicRS.K
theorem _root_.solution {h d : ℕ} (ht : tstR h d = true) (h2 : 2 ≤ h) :
    3 * ((h : ℝ) + 1) < 10 * (d : ℝ) * Real.log ((h : ℝ) / 2) := by
  simp only [tstR, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at ht
  obtain ⟨hd, hp⟩ := ht
  have hB : 0 < 10 * d * 6931471803 := by positivity
  have hlt0 : 7680000000000 * (h + 1) < (10 * d * 6931471803) * (7680000000000 * (h + 1) / (10 * d * 6931471803) + 1) :=
    Nat.lt_mul_div_succ _ hB
  generalize 7680000000000 * (h + 1) / (10 * d * 6931471803) = q at hp hlt0
  have hlt : ((7680000000000 * (h + 1) : ℕ) : ℝ) < ((10 * d * 6931471803) * (q + 1) : ℕ) := by
    exact_mod_cast hlt0
  push_cast at hlt
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hpow : ((2 : ℝ)) ^ (q + 257) ≤ (h : ℝ) ^ 256 := by exact_mod_cast hp
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hl2 : Real.log ((h : ℝ) / 2) = Real.log h - Real.log 2 := Real.log_div hh0.ne' (by norm_num)
  have hB2 : ((q : ℝ) + 1) * Real.log 2 ≤ 256 * Real.log ((h : ℝ) / 2) := by
    rw [hl2]; push_cast at hlog; linarith
  have hL2 := Real.log_two_gt_d9
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hC : ((q : ℝ) + 1) * (10 * d) * 0.6931471803 ≤ ((q : ℝ) + 1) * (10 * d) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hL2.le (by positivity)
  have hE : (10 * (d : ℝ)) * (((q : ℝ) + 1) * Real.log 2) ≤ (10 * (d : ℝ)) * (256 * Real.log ((h : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hB2 (by positivity)
  nlinarith
end PI.PrimesDyadicRS.K
