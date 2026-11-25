-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_vge_vN__94db92c523bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:18.816383+00:00
-- url     : https://prove2.me/submissions/be582be0-9e91-4a75-9daf-6674f2bcc3b0

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
theorem _root_.solution (n : ℕ) : vge v (vN v n) (n : K) := by
  rw [vge_iff']
  intro m hm
  unfold vN
  rw [hm]; simp
end Formalism.MainNotions.PlaneGram
