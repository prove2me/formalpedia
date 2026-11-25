-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NullSmaller_ringKrullDim_le_of_lt_succ_dc2eac2098d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:57.676429+00:00
-- url     : https://prove2.me/submissions/680be3c0-156c-4ff4-a120-c7f4dca858c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller

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
open MvPolynomial MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NullSmaller
theorem _root_.solution {R : Type*} [CommRing R] {k : ℕ}
    (h : ringKrullDim R < ((k + 1 : ℕ) : WithBot ℕ∞)) : ringKrullDim R ≤ (k : WithBot ℕ∞) := by
  generalize ringKrullDim R = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe a =>
      have h' : a < k + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.1 h'
end NullSmaller
end GroundTheory.Heights₂.Heights
