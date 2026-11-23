-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fiG_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:36.41799+00:00
-- url     : https://prove2.me/submissions/cea21aef-01e4-4a86-9a88-2670c179a212

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : ℕ} {Ω : Set (Fin f → ℝ)} {h : (Fin f → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (tube f Ω)) (ν : Fin f → ℤ) :
    DifferentiableOn ℂ (fiG h ν) (tube f Ω) := by
  have hd : Differentiable ℂ
      (fun s : Fin f → ℂ => Complex.exp (-2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * s k)) := by
    fun_prop
  exact hh.mul hd.differentiableOn
end ReciprocityTheory.L2DbarEstimates.Y
