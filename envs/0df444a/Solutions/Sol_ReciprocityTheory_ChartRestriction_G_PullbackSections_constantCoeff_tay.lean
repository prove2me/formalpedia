-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.constantCoeff_tay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:13.807151+00:00
-- url     : https://prove2.me/submissions/da5fd4d5-8d78-4635-9d60-fd9ed987bf5a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_coeff_tay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (θ : (Fin g → ℂ) → ℂ) (s : Multiset (Fin g → ℂ)) :
    constantCoeff (tay θ s) = mD θ 0 s := by
  first
  | (rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_tay]
     simp [dirs, fct])
  | (show tay θ s 0 = _
     simp [tay, dirs, fct])
end ReciprocityTheory.ChartRestriction.G.PullbackSections
