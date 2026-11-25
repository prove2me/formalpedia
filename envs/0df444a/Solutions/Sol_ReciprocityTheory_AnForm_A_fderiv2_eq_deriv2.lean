-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.fderiv2_eq_deriv2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:10.183746+00:00
-- url     : https://prove2.me/submissions/ab84eb36-cdb5-469a-b430-35d299799558

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_hasDerivAt_line_fderiv
import Theorems.Thm_ReciprocityTheory_AnForm_A_line_deriv_eventually

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
    fderiv ℝ (fderiv ℝ φ) z w w = deriv (deriv (fun s : ℝ => φ (z + s • w))) 0 := by
  have e : deriv (fun s : ℝ => φ (z + s • w)) =ᶠ[𝓝 0] fun s => fderiv ℝ φ (z + s • w) w :=
    (line_deriv_eventually hU hφ hz w).mono fun s hs => hs.deriv
  rw [e.deriv_eq, (hasDerivAt_line_fderiv hU hφ hz w).deriv]
end ReciprocityTheory.AnForm.A
