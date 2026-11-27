-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_exists_dim_3f23875fc98c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:15.695431+00:00
-- url     : https://prove2.me/submissions/fa711f73-1b2f-45fb-b5dd-36478fca5a96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace IrreducibleBasicOpenConnected
theorem _root_.solution {n : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W.IsPrime) : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d := by
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ W) := Ideal.Quotient.nontrivial_iff.mpr hW.ne_top
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ n := by
    have := ringKrullDim_le_of_surjective (Ideal.Quotient.mk W) Ideal.Quotient.mk_surjective
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at this
    simpa [Nat.card_eq_fintype_card] using this
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h0 hle
  induction D using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd hle (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)))
    | coe d => exact ⟨d, rfl⟩
end IrreducibleBasicOpenConnected
end GroundTheory.Heights₂.Heights.HilbertSamuel
