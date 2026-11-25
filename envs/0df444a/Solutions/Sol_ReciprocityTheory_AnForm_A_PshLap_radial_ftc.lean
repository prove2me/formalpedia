-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.radial_ftc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:43.111864+00:00
-- url     : https://prove2.me/submissions/f989658c-17d1-48d0-ba58-8f518b92c078

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasDerivAt_circleMap_radius
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_circleMap_mem_closedBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (hg : ∀ x ∈ V, HasFDerivAt g (G x) x) (hGc : ContinuousOn G V)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : closedBall (0:ℂ) R ⊆ V) (θ : ℝ) :
    g (circleMap 0 R θ) - g 0 = ∫ r in (0:ℝ)..R, G (circleMap 0 r θ) (circleMap 0 1 θ) := by
  have hmem : ∀ r ∈ uIcc (0:ℝ) R, circleMap 0 r θ ∈ V := fun r hr => by
    rw [uIcc_of_le hR0] at hr
    exact hR (circleMap_mem_closedBall hr.1 hr.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => g (circleMap 0 r θ))
    (fun r hr => (hg _ (hmem r hr)).comp_hasDerivAt r (hasDerivAt_circleMap_radius r θ)) ?_
  · have h0 : circleMap 0 0 θ = 0 := by simp [circleMap]
    rw [h, h0]
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.clm_apply ?_ continuousOn_const
    exact hGc.comp (Continuous.continuousOn (by unfold circleMap; fun_prop)) (fun r hr => hmem r hr)
end ReciprocityTheory.AnForm.A.PshLap
