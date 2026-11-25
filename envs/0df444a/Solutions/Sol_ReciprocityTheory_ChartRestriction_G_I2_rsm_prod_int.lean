-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rsm_prod_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:01.150109+00:00
-- url     : https://prove2.me/submissions/c84587f7-ddad-4d6a-a21f-4b729952aa61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric Set
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (N : ℕ) (F : EuclideanSpace ℂ (Fin N) → ℂ) (hF : Continuous F) (r : ℝ) :
    Integrable (fun p : EuclideanSpace ℂ (Fin N) × ℝ =>
        Real.exp (-‖p.1‖ ^ 2) * ‖F (circleMap 0 1 p.2 • p.1)‖ ^ 2)
      ((volume.restrict (closedBall 0 r)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
  have hc : Continuous fun p : EuclideanSpace ℂ (Fin N) × ℝ => circleMap 0 1 p.2 • p.1 :=
    ((continuous_circleMap 0 1).comp continuous_snd).smul continuous_fst
  have hg : Continuous fun p : EuclideanSpace ℂ (Fin N) × ℝ =>
      Real.exp (-‖p.1‖ ^ 2) * ‖F (circleMap 0 1 p.2 • p.1)‖ ^ 2 := by
    first
      | exact (Real.continuous_exp.comp ((continuous_fst.norm.pow 2).neg)).mul ((hF.comp hc).norm.pow 2)
      | fun_prop
  rw [Measure.prod_restrict]
  exact (hg.continuousOn.integrableOn_compact ((isCompact_closedBall 0 r).prod isCompact_Icc)).mono_set
    (Set.prod_mono subset_rfl Set.Ioc_subset_Icc_self)
end ReciprocityTheory.ChartRestriction.G.I2
