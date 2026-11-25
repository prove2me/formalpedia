-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_succ_le_of_ringKrullDim_quotient_fb5ca6b44376
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:30.226807+00:00
-- url     : https://prove2.me/submissions/a09cadc3-596c-412b-832f-fecf4571461d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGramLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeSheetGram

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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by
  have h := ringKrullDim_quotient_le J
  rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  exact_mod_cast h
end GroundTheory.Heights₂.Heights
