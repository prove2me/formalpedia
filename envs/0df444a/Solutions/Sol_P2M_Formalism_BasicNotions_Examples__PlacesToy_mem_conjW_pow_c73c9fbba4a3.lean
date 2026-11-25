-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__PlacesToy_mem_conjW_pow_c73c9fbba4a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:59.788801+00:00
-- url     : https://prove2.me/submissions/d4a72302-296c-4d65-a3e5-1ee21a05d9b3

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_conjW_asIdeal__1c4fc9345533

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (n : ℕ) :
    r ∈ (conjW w).asIdeal ^ n ↔ starO r ∈ w.asIdeal ^ n := by
  rw [conjW_asIdeal', ← Ideal.map_pow, ← Ideal.symm_apply_mem_of_equiv_iff, starO_symm]
end Formalism.BasicNotions.Examples₂.PlacesToy
