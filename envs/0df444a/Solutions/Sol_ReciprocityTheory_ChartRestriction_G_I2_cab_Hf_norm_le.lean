-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_Hf_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:08.753804+00:00
-- url     : https://prove2.me/submissions/fa681f33-ccf7-4d36-82c8-f2ec34ea0acf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (v η : EuclideanSpace ℂ ι) : ‖Hf v η‖ ≤ ‖v‖ * ‖η‖ := by
  have : Hf v η = inner ℂ η v := by
    unfold Hf; simp [PiLp.inner_apply]
  rw [this, mul_comm]
  exact norm_inner_le_norm _ _
end ReciprocityTheory.ChartRestriction.G.I2
