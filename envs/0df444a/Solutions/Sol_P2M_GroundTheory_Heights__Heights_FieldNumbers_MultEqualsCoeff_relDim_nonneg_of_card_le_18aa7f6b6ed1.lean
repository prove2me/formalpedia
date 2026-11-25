-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_relDim_nonneg_of_card_le_18aa7f6b6ed1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:29.196797+00:00
-- url     : https://prove2.me/submissions/40a5270a-9a8e-4651-89ce-fe6aea93bd44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMultEqualsCoeff

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
variable {K : Type*}
variable [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
theorem _root_.solution (I : Ideal (MRing ι F))
    (h : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I)) : 0 ≤ relDim I := by
  unfold relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe e =>
      have he : Fintype.card K ≤ e := by exact_mod_cast h
      have : (0 : WithTop ℤ) ≤ WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) (e : ℕ∞) := by
        change (0 : WithTop ℤ) ≤ (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ)
        exact_mod_cast (by omega : (0 : ℤ) ≤ (e : ℤ) - Fintype.card K)
      exact WithBot.coe_le_coe.mpr this
end GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
