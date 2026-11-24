-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_monomial_c1481e7819e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:22:14.536177+00:00
-- url     : https://prove2.me/submissions/2a418a4f-671c-4db4-bb02-841f09bba0e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (l v : Fin m → ℕ) :
    cf l (monomial (ex v) (1 : ℚ)) = if l = v then 1 else 0 := by
  unfold cf
  rw [coeff_monomial]
  by_cases h : l = v
  · simp [h]
  · rw [if_neg, if_neg h]
    intro h'
    apply h
    have := congrArg (fun d : Fin m →₀ ℕ => (d : Fin m → ℕ)) h'
    simpa using this.symm
end GroundTheory.Heights₂.Heights.RestTerms.Comb
