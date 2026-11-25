-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptOn_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:19.17882+00:00
-- url     : https://prove2.me/submissions/e131ad46-2cf9-412b-ab5c-8f97ef57c7b3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) (b s : Fin d) :
    coeff (Finsupp.single s 1) (ptOn a ga b) = if s = a then tangent ga b else 0 := by
  rw [ptOn, PowerSeries.coeff_subst_single]
  by_cases hs : s = a
  · subst hs
    simp [tangent]
  · simp [Finsupp.single_apply, hs, Ne.symm hs]
end ReciprocityTheory.ChartRestriction.G.Sh
