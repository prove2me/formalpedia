-- Prove2me | solution 1 for P2M_PI_Landherr__unitNormLoc_add_lt_ceb1586227f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:42.834858+00:00
-- url     : https://prove2.me/submissions/735faf4b-c995-4f9d-bba7-e38aa098c035

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
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} {r : ℝ}
    (hx : ‖x‖ < r) (hy : ‖y‖ < r) : ‖x + y‖ < r := (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
end PI.Landherr₃
