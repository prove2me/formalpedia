-- Prove2me | solution 1 for SchwartzMap.reference_basis_fundamental_region_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/26bc359a-85ad-42eb-a754-c4a7ed0a3345

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstant_axis_cell_volume_formula

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform Real
open MeasureTheory Module
open SchwartzMap
variable {d : ℕ}
namespace SchwartzMap
theorem _root_.solution :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).real
        (ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)) = 1 := by
  have hdomain :
      ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) =
        axisAlignedCell (d := d) 1 := by
    ext x
    simp [ZSpan.mem_fundamentalDomain, axisAlignedCell]
  rw [Measure.real, hdomain, PeriodicConstant.axis_cell_volume_formula]
  norm_num
end SchwartzMap
