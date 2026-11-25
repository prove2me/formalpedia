-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__PlacesToy_vAdd_conjW_59bcae034668
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:32.895241+00:00
-- url     : https://prove2.me/submissions/b2b3e4a8-3b3e-4287-8ecc-f9328cd7f6b7

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_valuation_conjW_8bb86d4edb22

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
namespace Formalism.BasicNotions.Examples₂.PlacesToy
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    vAdd (conjW w) x = vAdd w (star x) := by
  unfold vAdd
  rw [valuation_conjW]
end Formalism.BasicNotions.Examples₂.PlacesToy
