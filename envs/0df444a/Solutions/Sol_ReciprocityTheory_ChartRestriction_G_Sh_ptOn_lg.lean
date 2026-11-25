-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptOn_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:48.497024+00:00
-- url     : https://prove2.me/submissions/a7fbf0ed-e76f-43a4-a6a5-4b0ff4c624d5

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptOn_hs

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
theorem _root_.solution (G : LogFGL v d) (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga)
    (b : Fin d) :
    subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve ga b) := by
  have hga : HasSubst ga := MvPowerSeries.hasSubst_of_constantCoeff_zero fun c => (h c).1
  show subst (ptOn a ga) (G.lg b) = PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (subst ga (G.lg b))
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hga (ptOn_hs a)]
  rfl
end ReciprocityTheory.ChartRestriction.G.Sh
