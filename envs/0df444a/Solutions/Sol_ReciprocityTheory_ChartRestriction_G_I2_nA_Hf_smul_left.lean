-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.nA_Hf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:27:04.403061+00:00
-- url     : https://prove2.me/submissions/81600a87-af4c-4594-be98-44c6c1878495

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (c : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (c • v) w = c * Hf v w := by
  simp [Hf, Finset.mul_sum, mul_assoc]
end ReciprocityTheory.ChartRestriction.G.I2
