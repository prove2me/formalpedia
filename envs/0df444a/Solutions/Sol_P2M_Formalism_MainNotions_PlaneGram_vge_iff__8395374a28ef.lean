-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_vge_iff__8395374a28ef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:57.259666+00:00
-- url     : https://prove2.me/submissions/2e48232d-d27c-49e2-9b3d-94af9d53b884

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight

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
theorem _root_.solution (a : ℝ) (x : K) : vge v a x ↔ ∀ n : ℚ, v x = (n : WithTop ℚ) → a ≤ n := by
  unfold vge vR
  cases h : v x with
  | top => simp
  | coe m =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe, WithTop.coe_inj]
    constructor
    · intro h1 n hn; rw [← hn]; exact h1
    · intro h1; exact h1 m rfl
end Formalism.MainNotions.PlaneGram
