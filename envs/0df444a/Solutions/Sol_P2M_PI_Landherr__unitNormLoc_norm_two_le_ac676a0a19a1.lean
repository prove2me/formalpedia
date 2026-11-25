-- Prove2me | solution 1 for P2M_PI_Landherr__unitNormLoc_norm_two_le_ac676a0a19a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:53:35.339439+00:00
-- url     : https://prove2.me/submissions/6a67da97-0358-4886-b80a-dbf3cb20f4e2

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
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] : ‖(2 : K)‖ ≤ 1 := by
  have h := IsUltrametricDist.norm_add_le_max (1 : K) 1
  rw [one_add_one_eq_two, norm_one, max_self] at h
  exact h
end PI.Landherr₃
