-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Hf_im_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:55.516872+00:00
-- url     : https://prove2.me/submissions/f189b7b8-08c3-490b-91c3-61902c6ae2e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (v : EuclideanSpace ℂ ι) : (Hf v 0).im = 0 := by
  simp [Hf]
end ReciprocityTheory.ChartRestriction.G.I2
