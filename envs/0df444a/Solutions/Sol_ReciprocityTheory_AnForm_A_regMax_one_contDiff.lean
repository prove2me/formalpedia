-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_one_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:04.447792+00:00
-- url     : https://prove2.me/submissions/d7b47671-7b1e-48eb-9c80-da144b524b25

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_hasCompactSupport
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_eq_conv

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
theorem _root_.solution : ContDiff ℝ ∞ (regMax (ι := ι) 1) := by
  rw [regMax_one_eq_conv]
  exact HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    kK_hasCompactSupport kK_contDiff continuous_tmax.locallyIntegrable
end ReciprocityTheory.AnForm.A
