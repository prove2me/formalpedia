-- Prove2me | solution 1 for PI.QmIndepW.qmIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:47.951016+00:00
-- url     : https://prove2.me/submissions/ead1dd9a-4685-4cc2-8bf9-8148df738949

import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepPoly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_QmIndep
import Theorems.Thm_PI_QmIndepW_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmIndepW
open Complex
namespace PI.QmIndepW
theorem _root_.solution : PI.RTTIndependence := by
  intro V _ _ x Y Y' hY hx A B
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  refine scalar (fun A B => φ (x A B)) Y Y' hY (fun c hc β n => ?_) A B
  have h := congrArg φ (hx c hc β n)
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
  exact h
end PI.QmIndepW
