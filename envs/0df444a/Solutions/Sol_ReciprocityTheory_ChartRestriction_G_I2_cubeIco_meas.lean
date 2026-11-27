-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cubeIco_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:15.340019+00:00
-- url     : https://prove2.me/submissions/e744ee51-78f5-4781-bed3-a0206a1ffc62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CubeIcoMeas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cubeIco_eq

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
theorem _root_.solution (κ : Type) [Finite κ] : MeasurableSet (cubeIco κ) := by
  rw [cubeIco_eq]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico
end ReciprocityTheory.ChartRestriction.G.I2
