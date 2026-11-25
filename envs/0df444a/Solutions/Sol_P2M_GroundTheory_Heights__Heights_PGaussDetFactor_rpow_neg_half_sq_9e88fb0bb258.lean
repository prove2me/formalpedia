-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussDetFactor_rpow_neg_half_sq_9e88fb0bb258
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:53.11201+00:00
-- url     : https://prove2.me/submissions/6e532225-481e-4be8-b91c-2562da82f19e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussDetFactor

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
open GroundTheory.Heights₂.Heights.PGaussDetFactor
namespace GroundTheory.Heights₂.Heights.PGaussDetFactor
theorem _root_.solution {d : ℝ} (hd : 0 < d) : (d ^ (-(1 / 2 : ℝ))) ^ 2 = d⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num
  exact Real.rpow_neg_one d
end GroundTheory.Heights₂.Heights.PGaussDetFactor
