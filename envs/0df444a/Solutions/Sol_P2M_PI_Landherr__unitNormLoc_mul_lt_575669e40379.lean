-- Prove2me | solution 1 for P2M_PI_Landherr__unitNormLoc_mul_lt_575669e40379
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:46.520853+00:00
-- url     : https://prove2.me/submissions/a8f873ff-0bff-46fb-8919-835d017aa86c

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
theorem _root_.solution {K : Type} [NormedField K] {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) :
    ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hx) hy
end PI.Landherr₃
