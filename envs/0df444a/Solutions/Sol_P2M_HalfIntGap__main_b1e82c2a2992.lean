-- Prove2me | solution 1 for P2M_HalfIntGap__main_b1e82c2a2992
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:26.835245+00:00
-- url     : https://prove2.me/submissions/bb11bcc1-b9c4-415b-9c7e-e9ab29719929

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HalfIntegerGap_IntGap
import Theorems.Thm_P2M_HalfIntGap__gap_673ecf939950

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HalfIntGap₂
namespace HalfIntGap₂
theorem _root_.solution : Formalism.MainNotions.Ext.CutB.cBHCGap := by
  intro N lam c hlam hc a b hab
  exact gap N lam c hlam hc a b hab
end HalfIntGap₂
