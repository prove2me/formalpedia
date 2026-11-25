-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_eq__c00dd98ec76c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:48.623928+00:00
-- url     : https://prove2.me/submissions/9aa0c982-763d-437a-b170-44bc9e6534a6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_eq

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
theorem _root_.solution (v w : EuclideanSpace ℂ ι) : (Hf v w).im = ⟪-(Complex.I • v), w⟫_ℝ := by
  rw [Hf_conj w v, Complex.conj_im, Hf_im_eq w v, inner_neg_left]
end ReciprocityTheory.ChartRestriction.G.I2
