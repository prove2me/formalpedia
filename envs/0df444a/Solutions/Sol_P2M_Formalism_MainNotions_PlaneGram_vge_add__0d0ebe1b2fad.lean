-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_vge_add__0d0ebe1b2fad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:17.428799+00:00
-- url     : https://prove2.me/submissions/e8a22048-0f08-4e78-b2e2-fcfd1b0565de

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_iff__8395374a28ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {a : ℝ} {x y : K} (hx : vge v a x) (hy : vge v a y) : vge v a (x + y) := by
  rw [vge_iff'] at *
  intro n hn
  have h := v.map_add x y
  rw [hn] at h
  rcases min_le_iff.mp h with h1 | h1
  · obtain ⟨m, hm, hmn⟩ := WithTop.le_coe_iff.mp h1
    exact (hx m hm).trans (by exact_mod_cast hmn)
  · obtain ⟨m, hm, hmn⟩ := WithTop.le_coe_iff.mp h1
    exact (hy m hm).trans (by exact_mod_cast hmn)
end Formalism.MainNotions.PlaneGram
