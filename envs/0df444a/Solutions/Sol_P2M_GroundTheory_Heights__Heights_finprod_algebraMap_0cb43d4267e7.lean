-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finprod_algebraMap_0cb43d4267e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:03.588115+00:00
-- url     : https://prove2.me/submissions/eca35dcb-92da-4435-b32e-46420e31c04c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {c : K} (hc : c ≠ 0) :
    ∏ᶠ w : FinitePlace L, w (algebraMap K L c) = (∏ᶠ v : FinitePlace K, v c) ^ finrank K L := by
  rw [FinitePlace.prod_eq_inv_abs_norm ((map_ne_zero _).mpr hc), FinitePlace.prod_eq_inv_abs_norm hc,
    ← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow]
  push_cast
  rw [abs_pow, inv_pow]
end GroundTheory.Heights₂.Heights
