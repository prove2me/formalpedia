-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_integral_smul__67d1bab69c28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:13.764797+00:00
-- url     : https://prove2.me/submissions/77682db6-8771-4b55-adb6-f3fa48adf2fb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial

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
variable {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)} {σ : Type}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {a : K} {F : MvPolynomial σ K} (ha : 0 ≤ v a) (hF : Integral v F) :
    Integral v (a • F) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_smul, smul_eq_mul, AddValuation.map_mul]
  exact add_nonneg ha (hF α)
end Formalism.MainNotions.PlaneGram
