-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_pt_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:00.676805+00:00
-- url     : https://prove2.me/submissions/669296c0-04f3-48e8-adee-fd692c32484d

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
theorem _root_.solution {E : Type*} [SeminormedAddCommGroup E] (a b : E) (X : ℝ) (hX : 0 ≤ X) :
    ENNReal.ofReal (‖a + b‖ ^ 2 * X) ≤
      2 * ENNReal.ofReal (‖a‖ ^ 2 * X) + 2 * ENNReal.ofReal (‖b‖ ^ 2 * X) := by
  have h1 : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  calc ENNReal.ofReal (‖a + b‖ ^ 2 * X) ≤ ENNReal.ofReal (2 * (‖a‖ ^ 2 * X) + 2 * (‖b‖ ^ 2 * X)) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = 2 * ENNReal.ofReal (‖a‖ ^ 2 * X) + 2 * ENNReal.ofReal (‖b‖ ^ 2 * X) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp
end ReciprocityTheory.L2DbarEstimates.F
