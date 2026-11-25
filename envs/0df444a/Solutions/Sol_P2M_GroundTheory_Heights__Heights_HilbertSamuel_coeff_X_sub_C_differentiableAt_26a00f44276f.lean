-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_X_sub_C_differentiableAt_26a00f44276f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:02.42482+00:00
-- url     : https://prove2.me/submissions/d0c1475e-6a59-4f0f-b518-675550ceb8c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceCoefficientsHolomorphic

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
open MvPolynomial Matrix Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {d : ℕ} (a : (Fin d → ℂ) → ℂ) (y₀ : Fin d → ℂ)
    (ha : DifferentiableAt ℂ a y₀) (k : ℕ) :
    DifferentiableAt ℂ (fun y => (Polynomial.X - Polynomial.C (a y)).coeff k) y₀ := by
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  by_cases hk : k = 0
  · subst hk
    simpa using ha.neg
  · simp only [hk, if_false]
    exact differentiableAt_const _
end GroundTheory.Heights₂.Heights.HilbertSamuel
