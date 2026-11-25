-- Prove2me | solution 1 for P2M_PI_Landherr__unitNormLoc_mul_le_3fe19474cadc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:50.26021+00:00
-- url     : https://prove2.me/submissions/9f957f65-f0c5-4b3f-b0a1-26085b864f7c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LandherrUnitNorm_UnitNormLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open PI PI.Landherr₃
namespace PI.Landherr₃
theorem _root_.solution {K : Type} [NormedField K] {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg x, norm_nonneg y]
end PI.Landherr₃
