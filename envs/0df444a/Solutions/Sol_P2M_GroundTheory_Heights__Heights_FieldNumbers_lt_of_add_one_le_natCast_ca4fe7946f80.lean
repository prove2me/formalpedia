-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_lt_of_add_one_le_natCast_ca4fe7946f80
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:44.986808+00:00
-- url     : https://prove2.me/submissions/d9f59da2-ec4f-4bf7-bc75-4e57e77dcad8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ n) : x < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top n))
    | coe a =>
      have : a + 1 ≤ n := by exact_mod_cast h
      exact_mod_cast (show a < n by omega)
end GroundTheory.Heights₂.Heights.FieldNumbers
