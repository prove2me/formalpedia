-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.ball_subset_Cy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:32:01.910005+00:00
-- url     : https://prove2.me/submissions/24db3242-7513-4502-964b-32062f089ade

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : Metric.ball (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) (1 / 2) ⊆ Cy ι r := by
  intro y hy i
  have h := (dist_le_pi_dist y (fun i : UpI ι r => if i.1.2.1 = i.1.2.2 then (3 / 2 : ℂ) else 0) i).trans_lt
    (Metric.mem_ball.1 hy)
  have h32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
    rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  constructor
  · intro hi
    simp only [hi, ↓reduceIte, Complex.dist_eq] at h
    have h1 := norm_sub_norm_le (y i) (3 / 2)
    have h2 := norm_sub_norm_le (3 / 2 : ℂ) (y i)
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  · intro hi
    simp only [hi, ↓reduceIte, dist_zero_right] at h
    linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
