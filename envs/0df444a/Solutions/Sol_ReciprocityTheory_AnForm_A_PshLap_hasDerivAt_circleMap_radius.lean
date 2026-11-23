-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.hasDerivAt_circleMap_radius
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:25.11557+00:00
-- url     : https://prove2.me/submissions/45062e01-9e65-4e57-9e38-dd37988b1efa

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {V : Set ℂ} {g : ℂ → ℝ} {G : ℂ → ℂ →L[ℝ] ℝ} {H : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap 0 s θ) (circleMap 0 1 θ) r := by
  have h := ((hasDerivAt_id r).ofReal_comp).mul_const (Complex.exp (θ * Complex.I))
  simpa [circleMap] using h
end ReciprocityTheory.AnForm.A.PshLap
