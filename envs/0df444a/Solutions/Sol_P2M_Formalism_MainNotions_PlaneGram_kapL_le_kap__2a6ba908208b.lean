-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_kapL_le_kap__2a6ba908208b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:19.564273+00:00
-- url     : https://prove2.me/submissions/7054b8bb-0880-4849-9c6a-535632298944

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_le_kap

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {L : Type} [Fintype L] (d : L → ℕ) :
    kapL p r d ≤ kap p r d := le_trans (le_add_of_nonneg_right (by positivity)) (kapL_le_kap hp hr d)
end Formalism.MainNotions.PlaneGram
