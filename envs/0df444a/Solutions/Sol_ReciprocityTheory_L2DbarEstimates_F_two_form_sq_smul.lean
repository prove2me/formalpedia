-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.two_form_sq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:54.232014+00:00
-- url     : https://prove2.me/submissions/de031c33-72d6-4363-8425-2a0e888c97b4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA

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
theorem _root_.solution (n : ℕ) (c : ℂ) (a : Fin n → Fin n → ℂ) :
    sq2 n (fun j k => c * a j k) = ‖c‖ ^ 2 * sq2 n a := by
  simp only [sq2, norm_mul, mul_pow, ← Finset.mul_sum]
  ring
end ReciprocityTheory.L2DbarEstimates.F
