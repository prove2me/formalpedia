-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_const_mul__5b9ac33622c6
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:03:09.977786+00:00
-- url     : https://prove2.me/submissions/d7cd1db2-47cd-40aa-8715-9f725020f4e5

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
    (hg : DifferentiableAt ℝ g y) : wdb n j (fun w => c * g w) y = c * wdb n j g y := by
  have h : fderiv ℝ (fun w => c * g w) y = c • fderiv ℝ g y := fderiv_const_mul hg c
  unfold ReciprocityTheory.L2DbarEstimates.wdb
  rw [h]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring



