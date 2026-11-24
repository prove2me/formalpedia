-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LocF_vcompat_8cc30d9947af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:50:17.838898+00:00
-- url     : https://prove2.me/submissions/055a8cad-e124-4680-900e-61570f185a02

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
theorem _root_.solution : letI := vrel v
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Compatible := .ofValuation _
end Formalism.BasicNotions.Examples₂.LocF
