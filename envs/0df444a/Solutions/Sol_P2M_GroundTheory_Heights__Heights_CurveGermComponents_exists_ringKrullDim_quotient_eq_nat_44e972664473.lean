-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveGermComponents_exists_ringKrullDim_quotient_eq_nat_44e972664473
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:46.555676+00:00
-- url     : https://prove2.me/submissions/3edef543-ffd5-4a6d-bbb6-ed496b3d3c3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveGermComponents

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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.CurveGermComponents
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.CurveGermComponents
theorem _root_.solution (W : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime] :
    ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (e : ℕ) := by
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) :=
    (ringKrullDim_quotient_le W).trans (by simp)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d at h0 h1 ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h0
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, WithBot.coe_le_coe] at h1
      exact absurd h1 (not_le.2 (ENat.natCast_lt_top n))
    | coe e => exact ⟨e, rfl⟩
end GroundTheory.Heights₂.Heights.CurveGermComponents
