-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_quot_bot_acd27392687d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:37:59.241845+00:00
-- url     : https://prove2.me/submissions/88307e9d-4745-4cba-9fc0-d1e618250632

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements

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
theorem _root_.solution (F : Type*) [Field F] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ (⊥ : Ideal (MvPolynomial (Fin n) F))) =
      ((n : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial (Fin n) F)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]
end GroundTheory.Heights₂.Heights
