-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TopDualBound_dim_lines_429b83e413a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:30.023835+00:00
-- url     : https://prove2.me/submissions/25beb1ad-521b-4a3c-81fc-b819a2437f2b

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
theorem _root_.solution {i : ℕ} (hi : 1 ≤ i) : ((1 * 1 * (i - 1) + 1 : ℕ) : ℝ) = i := by
  congr 1; omega
end GroundTheory.Heights₂.Heights.TopDualBound
