-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.norm_sphMonomL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:05.261691+00:00
-- url     : https://prove2.me/submissions/1f75f315-821e-4422-af34-f4d621cafa16

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable (N : ℕ)
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (z : Fin N → ℂ) : ‖sphMonomL N z‖ = Real.sqrt (sqN z) := by
  rw [EuclideanSpace.norm_eq]
  rfl
end ReciprocityTheory.GeometryOfNumbersTheory
