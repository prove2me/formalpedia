-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.eq_integral_radial_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:39.399904+00:00
-- url     : https://prove2.me/submissions/6453e7b0-3f9f-43b9-ac2d-205790ca7b42

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasDerivAt_circleMap_radius
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_hasDerivAt_comp_radius
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshLap_clm_circleMap
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
theorem _root_.solution (hGd : ∀ x ∈ V, HasFDerivAt G (H x) x) (hGc : ContinuousOn G V)
    (hHc : ContinuousOn H V) {R : ℝ} (hR0 : 0 ≤ R) (hR : closedBall (0:ℂ) R ⊆ V) (θ : ℝ) :
    G (circleMap 0 R θ) (circleMap 0 R θ) = ∫ s in (0:ℝ)..R,
      (s * H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        G (circleMap 0 s θ) (circleMap 0 1 θ)) := by
  have hmem : ∀ r ∈ uIcc (0:ℝ) R, circleMap 0 r θ ∈ V := fun r hr => by
    rw [uIcc_of_le hR0] at hr
    exact hR (circleMap_mem_closedBall hr.1 hr.2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => G (circleMap 0 r θ) (circleMap 0 r θ))
    (f' := fun s => s * H (circleMap 0 s θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
        G (circleMap 0 s θ) (circleMap 0 1 θ))
    (fun r hr => by
      have h1 := (hasDerivAt_comp_radius r θ (hGd _ (hmem r hr))).clm_apply
        (hasDerivAt_circleMap_radius r θ)
      refine h1.congr_deriv ?_
      rw [clm_circleMap (H (circleMap 0 r θ) (circleMap 0 1 θ)) r θ]) ?_
  · have h0 : circleMap 0 0 θ = 0 := by simp [circleMap]
    rw [h, h0, map_zero, sub_zero]
  · apply ContinuousOn.intervalIntegrable
    have hc : ContinuousOn (fun r : ℝ => circleMap 0 r θ) (uIcc 0 R) :=
      Continuous.continuousOn (by unfold circleMap; fun_prop)
    refine ContinuousOn.add (ContinuousOn.mul continuousOn_id ?_) ?_
    · exact ((hHc.comp hc (fun r hr => hmem r hr)).clm_apply continuousOn_const).clm_apply
        continuousOn_const
    · exact (hGc.comp hc (fun r hr => hmem r hr)).clm_apply continuousOn_const
end ReciprocityTheory.AnForm.A.PshLap
