-- Prove2me | solution 2 for ReciprocityTheory.AnForm.A.continuous_tmax_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:20.082174+00:00
-- url     : https://prove2.me/submissions/b1672243-615b-4381-ae17-18e5655e1662

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax

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
theorem _root_.solution (η : ℝ) (t : ι → ℝ) :
    Continuous (fun h : ι → ℝ => tmax (fun j => t j + η * h j)) := continuous_tmax.comp
    (continuous_pi fun j => continuous_const.add (continuous_const.mul (continuous_apply j)))
end ReciprocityTheory.AnForm.A
