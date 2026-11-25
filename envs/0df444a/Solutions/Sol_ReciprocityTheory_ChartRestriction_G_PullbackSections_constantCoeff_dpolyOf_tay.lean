-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.constantCoeff_dpolyOf_tay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:42.957155+00:00
-- url     : https://prove2.me/submissions/d5c186f8-64c8-4b3a-ab64-58c44b077602

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_constantCoeff_dmonOf_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_polyDeriv_eq_mD

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
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} [Fintype ι]
    (u : ι → Fin g → ℂ) (P : MvPolynomial ι ℂ) :
    constantCoeff (DpolyOf (addF ℂ g) u P (tay θ 0)) = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u θ 0 := by
  unfold DpolyOf
  rw [polyDeriv_eq_mD hθ, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_C, constantCoeff_dmonOf_tay hθ]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
