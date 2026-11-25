-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussShellSum_exp_neg_nat_4b21dec2f2be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:55.608799+00:00
-- url     : https://prove2.me/submissions/380c5aee-7ca7-461b-ab52-6554ac59647c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussShellSum

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
open Real
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussShellSum
namespace GroundTheory.Heights₂.Heights.PGaussShellSum
theorem _root_.solution (m : ℕ) : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring
end GroundTheory.Heights₂.Heights.PGaussShellSum
