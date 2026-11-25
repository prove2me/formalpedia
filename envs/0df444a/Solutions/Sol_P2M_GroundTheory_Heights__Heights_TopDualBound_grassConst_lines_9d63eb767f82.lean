-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TopDualBound_grassConst_lines_9d63eb767f82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:32.27526+00:00
-- url     : https://prove2.me/submissions/969cde18-aa6f-4681-8f41-249ad5ac782e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualTopBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.TopDualBound
namespace GroundTheory.Heights₂.Heights.TopDualBound
theorem _root_.solution {i : ℕ} (hi : 1 ≤ i) : grassConst 1 1 (i - 1) = 1 / 2 * Real.log i := by
  have h : (1 : ℝ) + ((i - 1 : ℕ) : ℝ) = i := by
    rw [Nat.cast_sub hi]; push_cast; ring
  simp only [grassConst, h]
  norm_num
end GroundTheory.Heights₂.Heights.TopDualBound
