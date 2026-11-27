-- Prove2me | solution 2 for PositivityTheory.ThKOwn.mulL_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:29.665498+00:00
-- url     : https://prove2.me/submissions/488d01d3-c06c-4f5e-a326-fa6dd8a39b91

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply
import Theorems.Thm_PositivityTheory_ThKOwn_mulL_apply

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
namespace PositivityTheory.ThKOwn
theorem _root_.solution (L : V →L[ℝ] ℝ) (m : ℕ) (f : 𝓢(V, ℂ)) (x : V) : (mulL L ^ m) f x = (L x : ℂ) ^ m * f x := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', ContinuousLinearMap.mul_apply, mulL_apply, ih]; ring
end PositivityTheory.ThKOwn
