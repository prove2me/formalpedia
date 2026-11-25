-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:16.719398+00:00
-- url     : https://prove2.me/submissions/ddd08c6e-c775-49da-8762-f0b839da32ad

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_mono
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_eq_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_continuous_tmax_shift
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_kK_mono

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
theorem _root_.solution (η : ℝ) : Monotone (regMax (ι := ι) η) := by
  intro s t hst
  rw [regMax_eq_kK, regMax_eq_kK]
  exact integral_kK_mono (continuous_tmax_shift η s) (continuous_tmax_shift η t) fun h _ =>
    tmax_mono fun j => by
      show s j + η * h j ≤ t j + η * h j
      linarith [hst j]
end ReciprocityTheory.AnForm.A
