-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__PlacesToy_valuation_conjW_8bb86d4edb22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:50.099812+00:00
-- url     : https://prove2.me/submissions/1821f884-70ac-41fb-a38b-a5fcd94b53d7

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_intValuation_conjW_50932005530f

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
    (conjW w).valuation K x = w.valuation K (star x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hs : star (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) =
      algebraMap (𝓞 K) K (starO a) / algebraMap (𝓞 K) K (starO b) := by
    rw [star_div₀]
    rfl
  rw [hs, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_conjW, intValuation_conjW]
end Formalism.BasicNotions.Examples₂.PlacesToy
