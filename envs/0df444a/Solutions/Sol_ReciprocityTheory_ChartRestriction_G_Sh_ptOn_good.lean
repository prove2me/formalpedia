-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptOn_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:10.444725+00:00
-- url     : https://prove2.me/submissions/914e5f15-0ec7-4248-9a52-02beff8fc724

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptIsIntV_iff


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
theorem _root_.solution (a : Fin d) {ga : Fin d → PowerSeries C} (h : IsCurve v ga) :
    PTGood v (ptOn a ga) := by
  intro b
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X a) _ (h b).1, ?_⟩
  show ∀ α, coeff α (ptOn a ga b) ∈ ptIntSub v
  intro e
  rw [ptOn, PowerSeries.coeff_subst_single]
  split_ifs
  · exact (ptIsIntV_iff _).mp ((h b).2 _)
  · exact (ptIntSub v).zero_mem
end ReciprocityTheory.ChartRestriction.G.Sh
