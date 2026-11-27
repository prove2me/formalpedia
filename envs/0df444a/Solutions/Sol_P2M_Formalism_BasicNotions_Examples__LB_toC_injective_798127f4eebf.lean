-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_toC_injective_798127f4eebf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:02.691355+00:00
-- url     : https://prove2.me/submissions/ff0872be-9800-4bf1-b029-a33ecfd45435

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_toOm_injective_5840bbd4a71e

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
theorem _root_.solution : Function.Injective (toC LL) := fun a b h =>
  toOm_injective LL ((algebraMap (PadicAlgCl l) ℂ_[l]).injective h)
end Formalism.BasicNotions.Examples₂.LB
