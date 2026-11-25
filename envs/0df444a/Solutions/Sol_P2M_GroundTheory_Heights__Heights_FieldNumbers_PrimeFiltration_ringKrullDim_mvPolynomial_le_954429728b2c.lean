-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_ringKrullDim_mvPolynomial_le_954429728b2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:53:07.617794+00:00
-- url     : https://prove2.me/submissions/5f041c42-6507-4d94-9889-2c280df3f330

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution (F : Type u) [Field F] (σ : Type) [Finite σ] :
    ringKrullDim (MvPolynomial σ F) ≤ Nat.card σ := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    rw [← ringKrullDim_eq_of_ringEquiv (renameEquiv F e).toRingEquiv, ← Nat.card_congr e]
    exact H
  | h_empty =>
    simp [ringKrullDim_eq_zero_of_field]
  | h_option IH =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft F _).toRingEquiv,
      Polynomial.ringKrullDim_of_isNoetherianRing, Finite.card_option, Nat.cast_add, Nat.cast_one]
    exact add_le_add IH le_rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
