-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_le_natCast_of_lt_natCast_succ_e06a86729995
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.72445+00:00
-- url     : https://prove2.me/submissions/7ddfe0df-69f3-4679-95cc-d75fbe8cd2cc

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
theorem _root_.solution {x : WithBot ℕ∞} {N : ℕ}
    (h : x < ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ N := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_natCast, WithBot.coe_lt_coe] at h
      exact absurd h (not_lt.mpr le_top)
    | coe a =>
      have : a < N + 1 := by exact_mod_cast h
      exact_mod_cast (show a ≤ N by omega)
end GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
