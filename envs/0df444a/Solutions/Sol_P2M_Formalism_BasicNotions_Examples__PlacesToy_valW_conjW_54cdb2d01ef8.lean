-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__PlacesToy_valW_conjW_54cdb2d01ef8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:07.291231+00:00
-- url     : https://prove2.me/submissions/2c0482ac-2152-42bf-9230-0217149d7a04

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_valW_zero_68fbcf1955bc
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_vAdd_conjW_59bcae034668

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
    valW (conjW w) x = valW w (star x) := by
  by_cases hx : x = 0
  · subst hx; rw [star_zero, valW_zero, valW_zero]
  have hx' : star x ≠ 0 := by rwa [Ne, star_eq_zero]
  rw [valW_of_ne _ hx, valW_of_ne _ hx', vAdd_conjW]
end Formalism.BasicNotions.Examples₂.PlacesToy
