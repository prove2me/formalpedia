-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hasDerivAt_line_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:31.990915+00:00
-- url     : https://prove2.me/submissions/18d86529-9c37-4fc5-988e-929517a45c11

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_hasDerivAt_line

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
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {φ : E → ℝ} {U : Set E} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    {z : E} (hz : z ∈ U) (w : E) :
    HasDerivAt (fun s : ℝ => fderiv ℝ φ (z + s • w) w) (fderiv ℝ (fderiv ℝ φ) z w w) 0 := by
  have h1 : ContDiffAt ℝ 2 φ z := hφ.contDiffAt (hU.mem_nhds hz)
  have h2 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (h1.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt one_ne_zero
  have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ φ (z + s • w)) (fderiv ℝ (fderiv ℝ φ) z w) 0 :=
    h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line z w 0) (by simp)
  simpa using h3.clm_apply (hasDerivAt_const (0 : ℝ) w)
end ReciprocityTheory.AnForm.A
