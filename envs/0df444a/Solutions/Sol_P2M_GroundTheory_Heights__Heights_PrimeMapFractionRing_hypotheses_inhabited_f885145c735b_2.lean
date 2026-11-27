-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_PrimeMapFractionRing_hypotheses_inhabited_f885145c735b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:05.200644+00:00
-- url     : https://prove2.me/submissions/a0ebf9d1-f6aa-40be-bc53-36d01a8b5b04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm

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
namespace PrimeMapFractionRing
theorem _root_.solution :
    Prime (X 0 : MvPolynomial (Fin 1) ℤ) ∧ ∀ a : ℤ, (X 0 : MvPolynomial (Fin 1) ℤ) ≠ C a :=
  ⟨X_prime, fun a h => by
    have h' := congrArg totalDegree h
    rw [totalDegree_X, totalDegree_C] at h'
    exact one_ne_zero h'⟩
end PrimeMapFractionRing
end GroundTheory.Heights₂.Heights
