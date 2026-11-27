-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.comm_wdb_wdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:36:21.295017+00:00
-- url     : https://prove2.me/submissions/a888b840-03d9-4201-98e9-b7d8110f9607

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_comm_fderiv_wdb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j k : Fin n) :
    wdb n j (wdb n k g) y = wdb n k (wdb n j g) y := by
  have S := hg.isSymmSndFDerivAt (by simp)
  have e1 : wdb n j (wdb n k g) y = (fderiv ℝ (wdb n k g) y (bas n j)
      + Complex.I * fderiv ℝ (wdb n k g) y (Complex.I • bas n j)) / 2 := rfl
  have e2 : wdb n k (wdb n j g) y = (fderiv ℝ (wdb n j g) y (bas n k)
      + Complex.I * fderiv ℝ (wdb n j g) y (Complex.I • bas n k)) / 2 := rfl
  rw [e1, e2, comm_fderiv_wdb g y hg k (bas n j), comm_fderiv_wdb g y hg k (Complex.I • bas n j),
    comm_fderiv_wdb g y hg j (bas n k), comm_fderiv_wdb g y hg j (Complex.I • bas n k),
    S (bas n k) (bas n j), S (bas n k) (Complex.I • bas n j),
    S (Complex.I • bas n k) (bas n j), S (Complex.I • bas n k) (Complex.I • bas n j)]
  ring
end ReciprocityTheory.L2DbarEstimates
