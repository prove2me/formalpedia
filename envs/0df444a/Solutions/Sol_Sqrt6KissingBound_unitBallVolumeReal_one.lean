-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:20:21.68088+00:00
-- url     : https://prove2.me/submissions/cdfc8e8d-36ef-4565-98b2-168c17d245ee

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_formula
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution : unitBallVolumeReal 1 = 2 := by
  rw [unitBallVolumeReal_formula 0]
  simp only [Nat.cast_one, zero_add, pow_one]
  change Real.sqrt Real.pi / Real.Gamma ((1 : ℝ) / 2 + 1) = 2
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Real.Gamma_one_half_eq]
  field_simp [hsp]
end Sqrt6KissingBound
