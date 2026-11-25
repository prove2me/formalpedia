-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Hf_im_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:15.27693+00:00
-- url     : https://prove2.me/submissions/175cd110-3729-41f9-acb2-4c053300a731

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
theorem _root_.solution (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf (r • v) w).im = r * (Hf v w).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, mul_assoc]
end ReciprocityTheory.ChartRestriction.G.I2
