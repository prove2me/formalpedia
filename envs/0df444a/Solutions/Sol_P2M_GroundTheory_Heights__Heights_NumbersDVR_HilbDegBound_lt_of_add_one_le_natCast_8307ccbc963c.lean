-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_lt_of_add_one_le_natCast_8307ccbc963c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.753466+00:00
-- url     : https://prove2.me/submissions/d8453b30-e292-4685-af7c-082a8efb158a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
theorem _root_.solution {x : WithBot ℕ∞} {N : ℕ} (h : x + 1 ≤ N) : x < N := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top N))
    | coe a =>
      have : a + 1 ≤ N := by exact_mod_cast h
      exact_mod_cast (show a < N by omega)
end GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
