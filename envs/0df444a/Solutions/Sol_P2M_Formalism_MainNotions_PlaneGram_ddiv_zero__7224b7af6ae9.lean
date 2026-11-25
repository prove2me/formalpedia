-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_ddiv_zero__7224b7af6ae9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:25.700504+00:00
-- url     : https://prove2.me/submissions/675f2893-133a-436a-8a7b-57b3cd279607

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_add


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
variable {σ : Type} [Fintype σ]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F : MvPolynomial σ K) : ddiv 0 F = F := by
  refine MvPolynomial.induction_on' F (fun α c => ?_) (fun F₁ F₂ h₁ h₂ => ?_)
  · rw [ddiv_monomial']
    simp [bin]
  · rw [ddiv_add, h₁, h₂]
end Formalism.MainNotions.PlaneGram
