-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_conj__8f8e283438b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:59.214423+00:00
-- url     : https://prove2.me/submissions/7bde150f-52fa-4bb4-99b4-4f7f2012197a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_fderiv_conj__6e58fe8880aa

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
namespace ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
theorem _root_.solution (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) :
    wdb n j (fun w => (starRingEnd ℂ) (g w)) y = (starRingEnd ℂ) (wd n j g y) := by
  simp only [wdb, wd, fderiv_conj', map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
