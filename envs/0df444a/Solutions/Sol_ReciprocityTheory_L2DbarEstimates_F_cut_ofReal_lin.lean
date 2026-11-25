-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_ofReal_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:56.769031+00:00
-- url     : https://prove2.me/submissions/b9e5e311-39c2-4164-8524-c294134b62f8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (p q a b c : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : c ≤ p * a + q * b) :
    ENNReal.ofReal c ≤ ENNReal.ofReal p * ENNReal.ofReal a + ENNReal.ofReal q * ENNReal.ofReal b := by
  calc ENNReal.ofReal c ≤ ENNReal.ofReal (p * a + q * b) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hp, ENNReal.ofReal_mul hq]
end ReciprocityTheory.L2DbarEstimates.F
