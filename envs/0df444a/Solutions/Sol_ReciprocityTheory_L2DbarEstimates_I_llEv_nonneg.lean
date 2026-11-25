-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.llEv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:03.223848+00:00
-- url     : https://prove2.me/submissions/f8017ef8-43a3-4fb0-ad04-5e9e8b7b0c38

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogLeviA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev
  exact div_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Real.exp_pos _).le)
    (sq_nonneg _)
end ReciprocityTheory.L2DbarEstimates.I
