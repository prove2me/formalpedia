-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.molli_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:55.539803+00:00
-- url     : https://prove2.me/submissions/1809a6e6-fba4-4203-ae17-b0f485a0ca57

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_thick
import Theorems.Thm_ReciprocityTheory_AnForm_A_phiC
import Theorems.Thm_ReciprocityTheory_AnForm_A_molli_eq_C
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_scaled_hasCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
variable (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hU : IsOpen U) (hφ : IsPsh U φ) {ε : ℝ} (hε : 0 < ε)
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) : ContDiffAt ℝ ∞ (molli ρ ε φ) z := by
  obtain ⟨δ, hδ, hδU⟩ := exists_thick hU hε.le hz
  obtain ⟨-, hi⟩ := phiC hU hφ (isCompact_closedBall z (ε + δ)) hδU
  have hg := (scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [molli_eq_C ρ hε (C := closedBall z (ε + δ)) (closedBall_subset_closedBall' (by linarith)),
    convolution_def]
  rfl
end ReciprocityTheory.AnForm.A
