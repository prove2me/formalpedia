-- Prove2me | solution 1 for PI.FockOneDegW.highest_weight_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:57.438083+00:00
-- url     : https://prove2.me/submissions/71636dc3-74bc-41c1-8d12-a8df5f8b7e1e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Theorems.Thm_PI_FockOneDegW_RedOps_hc_lowOp
import Theorems.Thm_FockRaiseLowGrade_eq_zero_of_hc
import Theorems.Thm_FockRaiseLowGrade_hc_hc
import Theorems.Thm_PI_FockOneDegW_harmIff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
open PI.FockOneDegW.RedOps
namespace PI.FockOneDegW
theorem _root_.solution : HcHarm := by
  intro p q r s e P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  apply FockRaiseLowGrade.eq_zero_of_hc
  intro e'
  rw [hc_lowOp, FockRaiseLowGrade.hc_hc]
  split_ifs with h
  · subst h
    rw [← hc_lowOp, hP c d hcd, map_zero]
  · exact map_zero _
end PI.FockOneDegW
