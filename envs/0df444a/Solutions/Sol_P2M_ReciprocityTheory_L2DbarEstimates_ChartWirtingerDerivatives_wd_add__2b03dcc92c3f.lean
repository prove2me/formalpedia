-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_add__2b03dcc92c3f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:03:12.183788+00:00
-- url     : https://prove2.me/submissions/a7c3834e-a746-4f94-92b0-98896d5032f4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section
theorem _root_.solution (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) : wd n j (fun w => g w + h w) y = wd n j g y + wd n j h y := by
  have h' : fderiv ℝ (fun w => g w + h w) y = fderiv ℝ g y + fderiv ℝ h y := fderiv_add hg hh
  unfold ReciprocityTheory.L2DbarEstimates.wd
  rw [h']
  simp only [_root_.add_apply]
  ring



