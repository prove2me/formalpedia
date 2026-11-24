-- Prove2me | solution 1 for PositivityTheory.ThKOwn.expo_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:48.180122+00:00
-- url     : https://prove2.me/submissions/2640d1c2-f4b6-493f-be96-04b29e91d2a6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open Filter Topology Complex GlobalTheory.CompanionTheory.OM.SchDiff GlobalTheory.CompanionTheory.OM.GaussSch
open scoped SchwartzMap ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (L : V →L[ℝ] ℝ) {Q : V → ℂ} {w : ℝ}
namespace PositivityTheory.ThKOwn
theorem _root_.solution (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2) {R : ℝ} {p : ℂ} (hp : ‖p‖ ≤ R) (x : V) :
    (expo L Q (p, x)).re ≤ (R * ‖L‖) ^ 2 / (2 * w) + -(w / 2) * ‖x‖ ^ 2 := by
  have h1 : (p * (L x : ℂ)).re ≤ R * ‖L‖ * ‖x‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, mul_assoc]
    have := L.le_opNorm x
    have h0 := (norm_nonneg p).trans hp
    gcongr
  have h2 : R * ‖L‖ * ‖x‖ ≤ (R * ‖L‖) ^ 2 / (2 * w) + w / 2 * ‖x‖ ^ 2 := by
    have : (R * ‖L‖) ^ 2 / (2 * w) + w / 2 * ‖x‖ ^ 2 - R * ‖L‖ * ‖x‖ = (R * ‖L‖ - w * ‖x‖) ^ 2 / (2 * w) := by
      field_simp
      ring
    have h3 : 0 ≤ (R * ‖L‖ - w * ‖x‖) ^ 2 / (2 * w) := by positivity
    linarith
  have h3 := hre x
  simp only [expo, Complex.add_re]
  linarith
end PositivityTheory.ThKOwn
