-- Prove2me | solution 1 for PositivityTheory.ThKOwn.family_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:23:03.438866+00:00
-- url     : https://prove2.me/submissions/3ea1b9f1-96c9-4494-b4c3-0c1daf5be6a3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply
import Theorems.Thm_PositivityTheory_ThKOwn_mulL_apply
import Theorems.Thm_PositivityTheory_ThKOwn_expo_tg
import Theorems.Thm_PositivityTheory_ThKOwn_family_bound
import Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_hasFDerivAt_family
import Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique


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
theorem _root_.solution (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2)
    {G : ℂ → 𝓢(V, ℂ)} (hG : ∀ z, ⇑(G z) = fun x => (cexp ∘ expo L Q) (z, x)) (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (z : ℂ) :
    HasDerivAt (fun p => T (G p)) (T (mulL L (G z))) z := by
  have hF : ContDiff ℝ ∞ (cexp ∘ expo L Q) := Complex.contDiff_exp.comp (expo_tg L hQ).1
  have h := hasFDerivAt_family hF z (family_bound L hQ hw hre z) G (fun v => v • mulL L (G z)) hG
    (fun v => by
      funext x
      have h1 := (hF.differentiable (by simp) (z, x)).hasFDerivAt.hasLineDerivAt (v, 0)
      have h2 : HasLineDerivAt ℝ (cexp ∘ expo L Q) (cexp (expo L Q (z, x)) * (v * L x)) (z, x) (v, 0) := by
        have a1 : HasDerivAt (fun t : ℝ => (z + (t : ℂ) * v) * (L x : ℂ) + Q x) (v * L x) 0 := by
          simpa using ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v).const_add z).mul_const (L x : ℂ)).add_const (Q x)
        have a2 := a1.cexp
        simp only [Complex.ofReal_zero, zero_mul, add_zero] at a2
        refine a2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
        simp [expo]
      rw [h1.unique h2, SchwartzMap.smul_apply, mulL_apply, hG]
      simp only [Function.comp, smul_eq_mul]
      ring)
    T ((ContinuousLinearMap.toSpanSingleton ℂ (T (mulL L (G z)))).restrictScalars ℝ) (fun v => by simp)
  exact (hasFDerivAt_of_restrictScalars ℝ h rfl).hasDerivAt.congr_deriv (by simp)
end PositivityTheory.ThKOwn
