-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:07.631425+00:00
-- url     : https://prove2.me/submissions/21ef6f71-5398-4ae4-8758-36a050748124

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {N : ℕ} {F : (Fin N → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {n : WithTop ℕ∞} : ContDiff ℂ n F := by
  have hA := ReciprocityTheory.AnForm.Osgood.osgood N Set.univ F isOpen_univ hF.differentiableOn
  exact contDiffOn_univ.mp (hA.contDiffOn uniqueDiffOn_univ)
end ReciprocityTheory.ChartRestriction.G.I2
