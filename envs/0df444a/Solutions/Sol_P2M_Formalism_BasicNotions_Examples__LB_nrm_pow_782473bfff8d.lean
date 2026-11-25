-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_nrm_pow_782473bfff8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:30.224738+00:00
-- url     : https://prove2.me/submissions/643eafc1-edd7-4683-8fcb-341613bc232e

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF

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
theorem _root_.solution (a : ↥(OL LL)) (n : ℕ) : nrm LL (a ^ n) = nrm LL a ^ n := norm_pow _ _
end Formalism.BasicNotions.Examples₂.LB
