-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_integral_sum__e111d2e1e1a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:37.527094+00:00
-- url     : https://prove2.me/submissions/6ae2770c-53b2-40e7-a18a-f0eea6d93d56

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_zero__c35e386c5486
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_add__439be00d43f6

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
theorem _root_.solution {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ K)
    (h : ∀ k ∈ s, Integral v (f k)) : Integral v (∑ k ∈ s, f k) := by
  exact Finset.sum_induction f (fun F => Integral v F) (fun _ _ hF hG => integral_add' hF hG)
    integral_zero' h
end Formalism.MainNotions.PlaneGram
