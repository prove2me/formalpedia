-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_const_mul__4f4e797ecfdd
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:03:09.362778+00:00
-- url     : https://prove2.me/submissions/8f678c7e-dcde-4e27-8ec0-56dc395d1f4f

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
theorem _root_.solution (n : ℕ) (j : Fin n) (c : ℂ) (g : V n → ℂ) (y : V n)
    (hg : DifferentiableAt ℝ g y) : wd n j (fun w => c * g w) y = c * wd n j g y := by
  have h : fderiv ℝ (fun w => c * g w) y = c • fderiv ℝ g y := fderiv_const_mul hg c
  unfold ReciprocityTheory.L2DbarEstimates.wd
  rw [h]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring



