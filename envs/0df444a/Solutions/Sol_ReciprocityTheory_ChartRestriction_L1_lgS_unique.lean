-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.lgS_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:26:42.960405+00:00
-- url     : https://prove2.me/submissions/48f502e5-e3b9-48c0-912d-7466f06a681d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eq_substInv_of_rightInverse
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_weierstrassLog_eq_substInv

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
theorem _root_.solution (t : PowerSeries K) (ht : constantCoeff t = 0) (h : (uSer g2 g3).subst t = X) :
    t = lgS g2 g3 := by
  exact (eq_substInv_of_rightInverse g2 g3 t ht h).trans (weierstrassLog_eq_substInv g2 g3).symm
end ReciprocityTheory.ChartRestriction.L1
