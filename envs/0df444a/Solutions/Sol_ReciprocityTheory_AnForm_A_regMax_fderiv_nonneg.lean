-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_fderiv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:51:25.721802+00:00
-- url     : https://prove2.me/submissions/c974dc13-d3e0-4d59-ad87-fb227c2f7a02

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_hasDerivAt_line
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_mono


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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {η : ℝ} (hη : 0 < η) (p e : ι → ℝ) (he : 0 ≤ e) :
    0 ≤ fderiv ℝ (regMax (ι := ι) η) p e := by
  have h1 := ((regMax_contDiff hη).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) (hasDerivAt_line p e 0) (by simp)
  rw [← h1.deriv]
  apply Monotone.deriv_nonneg
  intro a b hab
  apply regMax_mono
  intro j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : 0 ≤ e j := he j
  nlinarith
end ReciprocityTheory.AnForm.A
