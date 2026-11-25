-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_sign_mul_self_630c9b7c6f03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:33.593332+00:00
-- url     : https://prove2.me/submissions/ca2f045e-2900-44df-a9f0-3c47313ecf5b

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
theorem _root_.solution (σ : Perm (Fin m)) :
    ((Perm.sign σ : ℤ) : ℚ) * ((Perm.sign σ : ℤ) : ℚ) = 1 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
end GroundTheory.Heights₂.Heights.RestTerms.Comb
