-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimeHomog_hypotheses_inhabited_0ebf35365ba4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:11.445191+00:00
-- url     : https://prove2.me/submissions/c2c2a898-8380-4ba7-b55c-36000ebe3a03

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace MinimalPrimeHomog
theorem _root_.solution :
    IsHomogIdeal (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).minimalPrimes :=
  ⟨(isProjPrime_point ℚ).isHomog, by
    have : (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).IsPrime := Ideal.isPrime_bot
    rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl⟩
end MinimalPrimeHomog
end GroundTheory.Heights₂.Heights
