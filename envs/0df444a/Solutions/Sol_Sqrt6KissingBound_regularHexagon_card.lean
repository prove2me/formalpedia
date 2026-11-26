-- Prove2me | solution 1 for Sqrt6KissingBound.regularHexagon_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:31:32.35565+00:00
-- url     : https://prove2.me/submissions/d0ef6032-a44c-4e57-a375-ff13dadb01d9

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_hexPoint_injective
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
theorem _root_.solution : regularHexagon.card = 6 := by
  classical
  have hcard : (Finset.univ.image hexPoint).card = Finset.univ.card :=
    Finset.card_image_iff.mpr hexPoint_injective.injOn
  simpa [regularHexagon] using hcard
end Sqrt6KissingBound
