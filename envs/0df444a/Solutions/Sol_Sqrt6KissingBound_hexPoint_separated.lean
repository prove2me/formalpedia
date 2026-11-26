-- Prove2me | solution 1 for Sqrt6KissingBound.hexPoint_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:25:33.634408+00:00
-- url     : https://prove2.me/submissions/e95057ac-5325-4d80-8e3f-52cd8ba90a7a

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_planePoint_inner
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
private lemma s3_pos_opt : 0 < s3_opt := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq_opt : s3_opt ^ 2 = 3 := by norm_num [s3_opt]
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution (i j : Fin 6) (hij : i ≠ j) :
    inner ℝ (hexPoint i) (hexPoint j) ≤ (1 : ℝ) / 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [hexPoint, planePoint_inner] at hij ⊢ <;>
    nlinarith [s3_sq_opt, s3_pos_opt]
end Sqrt6KissingBound
