-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Hf_im_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:14.085897+00:00
-- url     : https://prove2.me/submissions/b68f93f2-3940-4641-980b-61ec06177622

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_conj

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
theorem _root_.solution (v w : EuclideanSpace ℂ ι) : (Hf v w).im = -(Hf w v).im := by
  rw [Hf_conj w v, Complex.conj_im]
end ReciprocityTheory.ChartRestriction.G.I2
