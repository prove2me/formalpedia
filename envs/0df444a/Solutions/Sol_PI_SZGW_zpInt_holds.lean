-- Prove2me | solution 1 for PI.SZGW.zpInt_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:14.27005+00:00
-- url     : https://prove2.me/submissions/45117316-ee9c-4e66-a6e9-a4383f8cadff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_ZcFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitZeroClosedness_IsClosedSimeqZero
import Theorems.Thm_PI_SZGW_isClosed_int
import Theorems.Thm_PI_BeDiagZp_ContPf_zc_continuous
import Theorems.Thm_PI_BeDiagZp_ContPf_zc_natCast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.SZGW
open PI.BeDiagZp.ContPf
namespace PI.SZGW
theorem _root_.solution : ZpInt := by
  intro p _ σ G hG hN c
  have hcl' := (isClosed_int hG).preimage zc_continuous
  refine PadicInt.denseRange_natCast.induction_on c hcl' ?_
  intro k
  show PI.BeDiagZp.IntegralMv _
  rw [zc_natCast]
  exact hN k
end PI.SZGW
