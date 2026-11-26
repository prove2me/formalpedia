-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_antitone_from_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:21:07.328636+00:00
-- url     : https://prove2.me/submissions/c040ad09-334d-4170-a5ca-fe2987177af6

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_add_two
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_five_gt_six
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_six_gt_seven
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
attribute [local simp] Sqrt6KissingBound.mem_tailBall


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
private lemma volume_descent_step {n : ℕ} (hn : 8 ≤ n)
    (hprev : unitBallVolumeReal (n - 2) ≤ unitBallVolumeReal (n - 3)) :
    unitBallVolumeReal n ≤ unitBallVolumeReal (n - 1) := by
  have hcast : ((n - 3 : ℕ) : ℝ) + 3 = (n : ℝ) := by
    exact_mod_cast (show n - 3 + 3 = n by omega)
  have hcast' : ((n - 4 : ℕ) : ℝ) + 3 = ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n - 4 + 3 = n - 1 by omega)
  have hvn : unitBallVolumeReal n =
      (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 2) := by
    simpa only [show n - 3 + 3 = n by omega,
      show n - 3 + 1 = n - 2 by omega, hcast]
      using unitBallVolumeReal_add_two (n - 3)
  have hvn1 : unitBallVolumeReal (n - 1) =
      (2 * Real.pi / ((n - 1 : ℕ) : ℝ)) * unitBallVolumeReal (n - 3) := by
    simpa only [show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 1 = n - 3 by omega, hcast']
      using unitBallVolumeReal_add_two (n - 4)
  rw [hvn, hvn1]
  have hn1pos : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hcoef : 2 * Real.pi / (n : ℝ) ≤ 2 * Real.pi / (n - 1 : ℕ) := by
    exact div_le_div_of_nonneg_left (by positivity) hn1pos
      (by exact_mod_cast Nat.sub_le n 1)
  have hV : 0 ≤ unitBallVolumeReal (n - 3) := measureReal_nonneg
  calc
    (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 2) ≤
        (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 3) :=
      mul_le_mul_of_nonneg_left hprev (by positivity)
    _ ≤ (2 * Real.pi / (n - 1 : ℕ)) * unitBallVolumeReal (n - 3) :=
      mul_le_mul_of_nonneg_right hcoef hV
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution (n : ℕ) (hn : 6 ≤ n) :
    unitBallVolumeReal n ≤ unitBallVolumeReal (n - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h6 : n = 6
    · subst n
      simpa using unitBallVolumeReal_five_gt_six.le
    by_cases h7 : n = 7
    · subst n
      simpa using unitBallVolumeReal_six_gt_seven.le
    have hn8 : 8 ≤ n := by omega
    exact volume_descent_step hn8 (ih (n - 2) (by omega) (by omega))
end Sqrt6KissingBound
