-- Prove2me | solution 1 for PositivityTheory.ThKOwn.kill_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:36.889806+00:00
-- url     : https://prove2.me/submissions/50ed8d49-4734-4e27-a722-de0364a11f5d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply
import Theorems.Thm_PositivityTheory_ThKOwn_exists_family
import Theorems.Thm_PositivityTheory_ThKOwn_family_deriv

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
    {g : 𝓢(V, ℂ)} (hg : ∀ x, g x = cexp (Q x)) (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (hT : ∀ m : ℕ, T ((mulL L ^ m) g) = 0)
    (z : ℂ) {f : 𝓢(V, ℂ)} (hf : ∀ x, f x = cexp (z * (L x : ℂ)) * g x) : T f = 0 := by
  choose G hG using exists_family L hQ hw hre
  have hd : ∀ (m : ℕ) p, HasDerivAt (fun p => T ((mulL L ^ m) (G p))) (T ((mulL L ^ (m + 1)) (G p))) p := fun m p => by
    have := family_deriv L hQ hw hre hG (T ∘L mulL L ^ m) p
    rw [pow_succ]
    exact this
  have hi : ∀ m : ℕ, iteratedDeriv m (fun p => T (G p)) = fun p => T ((mulL L ^ m) (G p)) := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      funext p
      rw [iteratedDeriv_succ, ih, (hd m p).deriv]
  have h0 : G 0 = g := by
    ext x
    simp [hG, hg, expo]
  have hz : G z = f := by
    ext x
    simp [hG, hg, hf, expo, Complex.exp_add]
  have hdiff : Differentiable ℂ fun p => T (G p) := fun p => by simpa using (hd 0 p).differentiableAt
  have := Complex.taylorSeries_eq_of_entire' 0 z hdiff
  simp only [hi, h0, hT, mul_zero, zero_mul, tsum_zero, hz] at this
  exact this.symm
end PositivityTheory.ThKOwn
