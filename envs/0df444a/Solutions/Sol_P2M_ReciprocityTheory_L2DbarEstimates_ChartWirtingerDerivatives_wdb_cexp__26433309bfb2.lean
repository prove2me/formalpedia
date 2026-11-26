-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_cexp__26433309bfb2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:03:11.51517+00:00
-- url     : https://prove2.me/submissions/2fb220e3-6c5f-4e2b-b72c-3a6afcb44646

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
theorem _root_.solution (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y) :
    wdb n j (fun w => Complex.exp (g w)) y = Complex.exp (g y) * wdb n j g y := by
  have h : fderiv ℝ (fun w => Complex.exp (g w)) y = Complex.exp (g y) • fderiv ℝ g y := hg.hasFDerivAt.cexp.fderiv
  unfold ReciprocityTheory.L2DbarEstimates.wdb
  rw [h]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring



