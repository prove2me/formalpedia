-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_toFrac_eq_iff_84d60766bad1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:06.036481+00:00
-- url     : https://prove2.me/submissions/2bb2043d-59ca-4d93-ab48-e3dbacbcb31f

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_toFrac_coe_70b127540ffe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (x : ↥LL.1) (a : ↥(OL LL)) :
    algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) a = toFrac LL x ↔ (a : ↥LL.1) = x := by
  rw [← toFrac_coe]
  exact (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm.injective.eq_iff
end Formalism.BasicNotions.Examples₂.LB
