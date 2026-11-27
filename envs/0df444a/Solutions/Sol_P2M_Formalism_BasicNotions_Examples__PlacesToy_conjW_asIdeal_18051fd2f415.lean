-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal_18051fd2f415
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:24.744847+00:00
-- url     : https://prove2.me/submissions/cce9674c-74b8-4661-8f63-34e2308e5380

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions.Examples₂.PlacesToy
variable {K : Type} [Field K] [NumberField K] [StarRing K]
omit [NumberField K]
namespace Formalism.BasicNotions.Examples₂.PlacesToy
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    (conjW w).asIdeal = w.asIdeal.comap ((starO (K := K)).symm : 𝓞 K →+* 𝓞 K) := rfl
end Formalism.BasicNotions.Examples₂.PlacesToy
