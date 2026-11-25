-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_TwistData_Dl_nonneg__c6f8a139e94f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:22.200542+00:00
-- url     : https://prove2.me/submissions/f90813bf-c0be-4999-a936-6706412db857

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_eC_nonneg__6cf7440067fb

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dl p C0 := by
  unfold Dl
  have := D.eC_nonneg' hp hr h1
  have h2 : (0 : ℝ) ≤ (D.r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
    linarith
  positivity
end Formalism.MainNotions.PlaneGram.TwistData
