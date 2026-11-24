-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.isOpen_shrink
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:32.886837+00:00
-- url     : https://prove2.me/submissions/f10151e7-eebf-4d0e-ab97-ce4c5fe979c5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_thick

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
theorem _root_.solution (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) : IsOpen (shrink U ε) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨δ, hδ, h⟩ := exists_thick hU hε.le hz
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  exact (closedBall_subset_closedBall' (by linarith)).trans h
end ReciprocityTheory.AnForm.A
