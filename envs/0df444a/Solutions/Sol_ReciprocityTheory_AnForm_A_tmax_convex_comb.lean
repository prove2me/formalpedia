-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tmax_convex_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:45.827345+00:00
-- url     : https://prove2.me/submissions/b4ca65f0-d42b-4ee0-9cd4-6e80e85572ed

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (x y : ι → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tmax (a • x + b • y) ≤ a * tmax x + b * tmax y := tmax_le fun i => by
  show a * x i + b * y i ≤ a * tmax x + b * tmax y
  exact add_le_add (mul_le_mul_of_nonneg_left (le_tmax x i) ha)
    (mul_le_mul_of_nonneg_left (le_tmax y i) hb)
end ReciprocityTheory.AnForm.A
