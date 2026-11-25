-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv_conv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:11.673801+00:00
-- url     : https://prove2.me/submissions/d5e4550d-4cb2-4dac-97ff-792d287cf55a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_hasCompactSupport


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
theorem _root_.solution {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    fderiv ℝ (convolution kK g (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
      convolution (fderiv ℝ kK) g ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ι → ℝ)) volume := by
  funext x
  exact (kK_hasCompactSupport.hasFDerivAt_convolution_left _ (kK_contDiff.of_le (by simp))
    hg.locallyIntegrable x).fderiv
end ReciprocityTheory.AnForm.A
