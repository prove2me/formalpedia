-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_toOm_injective_5840bbd4a71e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:34:13.036621+00:00
-- url     : https://prove2.me/submissions/0e0708bb-2183-4b14-bc73-3c9812b20c1c

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
theorem _root_.solution : Function.Injective (toOm LL) := fun a b h => Subtype.ext (Subtype.ext h)
end Formalism.BasicNotions.Examples₂.LB
