-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_rightInverse_weierstrassExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:03.063961+00:00
-- url     : https://prove2.me/submissions/fa502942-e20d-4433-94ad-f87715fbb12a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [Field K] (g2 g3 : K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X := ⟨(uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3), PowerSeries.constantCoeff_substInvOfIsUnit _ _,
  PowerSeries.subst_substInvOfIsUnit_right _ (uSer_const g2 g3) _⟩
end ReciprocityTheory.ChartRestriction.L1
