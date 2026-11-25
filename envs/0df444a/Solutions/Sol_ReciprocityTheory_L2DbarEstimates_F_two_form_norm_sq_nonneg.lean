-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.two_form_norm_sq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:51.374919+00:00
-- url     : https://prove2.me/submissions/c697c34f-ac93-4fa0-8864-842f46b77833

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA

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
theorem _root_.solution (n : ℕ) (σ : Fin n → Fin n → ℂ) : 0 ≤ sq2 n σ := by
  unfold sq2
  first
  | positivity
  | exact div_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (by norm_num)
end ReciprocityTheory.L2DbarEstimates.F
