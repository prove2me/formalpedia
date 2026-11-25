-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal__1c4fc9345533
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:31:59.744147+00:00
-- url     : https://prove2.me/submissions/600e6e84-cade-4917-9f42-86bd89342cb0

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
    (conjW w).asIdeal = w.asIdeal.map (starO (K := K)) := by
  ext x
  rw [← Ideal.symm_apply_mem_of_equiv_iff]
  rfl
end Formalism.BasicNotions.Examples₂.PlacesToy
