-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_TwistData_kapD_nonneg__d58e933b9fd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:24.491802+00:00
-- url     : https://prove2.me/submissions/bec1908c-3cbd-4bbe-9ce4-d311144775d3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
import Theorems.Thm_Formalism_MainNotions_PlaneGram_kap_ge_card


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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) : 0 ≤ D.kapD p := by
  unfold kapD
  refine le_trans ?_ (kap_ge_card hp hr D.dO)
  positivity
end Formalism.MainNotions.PlaneGram.TwistData
