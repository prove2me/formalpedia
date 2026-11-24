-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.mult_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:48.760473+00:00
-- url     : https://prove2.me/submissions/256966d8-2083-484c-9e0d-6f24c85e03b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lgS_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_uSer_subst_lgS

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
theorem _root_.solution (b : K) (e : PowerSeries K) (he : constantCoeff e = 0)
    (h : (lgS g2 g3).subst e = C b * lgS g2 g3) : e = (uSer g2 g3).subst (C b * lgS g2 g3) := by
  have hl := HasSubst.of_constantCoeff_zero (lgS_const g2 g3)
  have hE := HasSubst.of_constantCoeff_zero he
  have h1 := PowerSeries.subst_comp_subst_apply hl hE (uSer g2 g3)
  rw [uSer_subst_lgS, PowerSeries.subst_X hE, h] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.L1
