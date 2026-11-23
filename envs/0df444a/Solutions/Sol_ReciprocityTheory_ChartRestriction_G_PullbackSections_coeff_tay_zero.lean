-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.coeff_tay_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:46.359817+00:00
-- url     : https://prove2.me/submissions/378cd7c3-bd5b-4742-90b2-22e1388b96f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_coeff_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_fct_ne_zero

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
theorem _root_.solution (θ : (Fin g → ℂ) → ℂ) (n : Fin 1 × Fin g →₀ ℕ) :
    fct n * coeff n (tay θ 0) = mD θ 0 (dirs n) := by
  rw [coeff_tay, add_zero]
  first
  | (field_simp [fct_ne_zero n]; done)
  | (field_simp [fct_ne_zero n]; ring)
  | exact mul_div_cancel₀ _ (fct_ne_zero n)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
