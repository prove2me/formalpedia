-- Prove2me | solution 1 for PositivityTheory.ThKOwn.exists_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:47.116105+00:00
-- url     : https://prove2.me/submissions/8cb845c7-0f09-4792-9e3f-b609d80b4b4f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_MulLPowApply
import Theorems.Thm_PositivityTheory_ThKOwn_expo_re

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
theorem _root_.solution (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2) (z : ℂ) :
    ∃ G : 𝓢(V, ℂ), ⇑G = fun x => (cexp ∘ expo L Q) (z, x) := by
  set B : ℝ := (‖z‖ * ‖L‖) ^ 2 / (2 * w)
  have hq : (fun x => z * (L x : ℂ) + Q x + -(B : ℂ)).HasTemperateGrowth :=
    (((Function.HasTemperateGrowth.const z).mul (Complex.ofRealCLM ∘L L).hasTemperateGrowth).add hQ).add
      (Function.HasTemperateGrowth.const _)
  refine ⟨cexp B • cexpSchwartz hq (half_pos hw) fun x => ?_, ?_⟩
  · have := expo_re L hw hre (le_refl ‖z‖) x
    simp only [expo] at this
    rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    linarith
  · funext x
    change cexp B * cexp (z * (L x : ℂ) + Q x + -(B : ℂ)) = cexp (z * (L x : ℂ) + Q x)
    rw [← Complex.exp_add]
    congr 1
    ring
end PositivityTheory.ThKOwn
