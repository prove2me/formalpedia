-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mem_ball_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:33.751583+00:00
-- url     : https://prove2.me/submissions/47eb7fc1-e97d-4c0c-82b1-577a27e854ac

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_lt_of_scaled_ne_zero


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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {y : Fin D → ℂ} (hy : ρ.scaled ε y ≠ 0)
    (z : Fin D → ℂ) : z - y ∈ closedBall z ε := by
  rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
  exact (norm_lt_of_scaled_ne_zero ρ hε hy).le
end ReciprocityTheory.AnForm.A
