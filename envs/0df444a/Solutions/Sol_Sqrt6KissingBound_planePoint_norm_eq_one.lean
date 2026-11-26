-- Prove2me | solution 1 for Sqrt6KissingBound.planePoint_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:25:57.0318+00:00
-- url     : https://prove2.me/submissions/9818e6f7-20ba-4846-b2db-6afc50483426

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_Optimality
import Theorems.Thm_Sqrt6KissingBound_planePoint_norm_sq

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    ‖planePoint x y‖ = 1 := by
  have hn : 0 ≤ ‖planePoint x y‖ := norm_nonneg _
  nlinarith [planePoint_norm_sq x y]
end Sqrt6KissingBound
