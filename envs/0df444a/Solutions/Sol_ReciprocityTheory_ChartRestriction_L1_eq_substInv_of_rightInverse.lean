-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.eq_substInv_of_rightInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:02.287183+00:00
-- url     : https://prove2.me/submissions/2650054d-54bb-4c80-8e61-b47e090bae6c

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
theorem _root_.solution (t : PowerSeries K) (ht : constantCoeff t = 0)
    (h : (uSer g2 g3).subst t = X) :
    t = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := by
  have h1 := PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero (uSer_const g2 g3))
    (HasSubst.of_constantCoeff_zero ht) ((uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3))
  rw [PowerSeries.subst_substInvOfIsUnit_left _ (uSer_const g2 g3), PowerSeries.subst_X (HasSubst.of_constantCoeff_zero ht),
    h, PowerSeries.X_subst] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.L1
