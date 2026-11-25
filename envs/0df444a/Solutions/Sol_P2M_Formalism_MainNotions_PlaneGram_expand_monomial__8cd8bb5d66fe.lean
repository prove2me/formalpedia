-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_expand_monomial__8cd8bb5d66fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:26.725317+00:00
-- url     : https://prove2.me/submissions/3f7d874c-a6f3-4a10-a510-1a01c9322e6b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


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
theorem _root_.solution {τ : Type} (P : ℕ) (d : τ →₀ ℕ) (c : K) :
    expand P (monomial d c) = monomial (P • d) c := by
  rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_eq,
    Finsupp.prod_of_support_subset _ Finsupp.support_smul (fun n e => (X n : MvPolynomial τ K) ^ e)
      (fun i _ => pow_zero _)]
end Formalism.MainNotions.PlaneGram
