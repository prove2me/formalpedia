-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LocF_finite_quot_bc450d17568e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:08.880836+00:00
-- url     : https://prove2.me/submissions/0f13a1f4-0606-4515-8bcc-809f79fff91b

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LocF
open NumberField IsDedekindDomain HeightOneSpectrum WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.BasicNotions.Examples₂.LocF
theorem _root_.solution : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
end Formalism.BasicNotions.Examples₂.LocF
