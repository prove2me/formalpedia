-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cubeIco_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:58.465355+00:00
-- url     : https://prove2.me/submissions/13e48fbe-4ba0-4d96-944f-1cdd46537509

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (κ : Type) : cubeIco κ = Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1 := by
  ext x
  simp [cubeIco, Set.mem_pi]
end ReciprocityTheory.ChartRestriction.G.I2
