-- Prove2me | solution 1 for Sqrt6KissingBound.planePoint_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:24:03.015279+00:00
-- url     : https://prove2.me/submissions/84823d1f-91fc-4bd4-9def-77b309c1e164

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution (x y u v : ℝ) :
    inner ℝ (planePoint x y) (planePoint u v) = x * u + y * v := by
  simp [planePoint, standardCoordinates, PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
end Sqrt6KissingBound
