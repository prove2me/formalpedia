-- Prove2me | solution 1 for P2M_PI_Landherr__unitNormLoc_norm_add_eq_left_e1f654c14de4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:48.301209+00:00
-- url     : https://prove2.me/submissions/49eaad2e-9e2e-475d-a5ad-4ce61e20d78d

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
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K)
    (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]
end PI.Landherr₃
