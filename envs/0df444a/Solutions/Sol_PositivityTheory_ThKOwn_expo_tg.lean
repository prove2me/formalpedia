-- Prove2me | solution 1 for PositivityTheory.ThKOwn.expo_tg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:00.684225+00:00
-- url     : https://prove2.me/submissions/0e4bafe1-5ce9-42eb-b995-926dba54624e

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
theorem _root_.solution (hQ : Q.HasTemperateGrowth) : (expo L Q).HasTemperateGrowth :=
  ((ContinuousLinearMap.fst ℝ ℂ V).hasTemperateGrowth.mul
    (Complex.ofRealCLM ∘L L ∘L ContinuousLinearMap.snd ℝ ℂ V).hasTemperateGrowth).add
    (hQ.comp (ContinuousLinearMap.snd ℝ ℂ V).hasTemperateGrowth)
end PositivityTheory.ThKOwn
