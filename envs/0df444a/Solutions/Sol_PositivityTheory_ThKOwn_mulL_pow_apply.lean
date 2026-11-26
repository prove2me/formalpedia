-- Prove2me | solution 1 for PositivityTheory.ThKOwn.mulL_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:48:40.570198+00:00
-- url     : https://prove2.me/submissions/6ccb834d-694e-4de7-9c0c-2e63484e436c

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
theorem _root_.solution (L : V →L[ℝ] ℝ) (m : ℕ) (f : 𝓢(V, ℂ)) (x : V) : (mulL L ^ m) f x = (L x : ℂ) ^ m * f x := by
  first
    | (induction m generalizing f with
       | zero => simp
       | succ m ih =>
         rw [pow_succ, ContinuousLinearMap.mul_apply, ih]
         have e : PositivityTheory.ThKOwn.mulL L f x = (L x : ℂ) * f x := by
           unfold PositivityTheory.ThKOwn.mulL
           rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
           rfl
         rw [e, pow_succ]
         ring)

