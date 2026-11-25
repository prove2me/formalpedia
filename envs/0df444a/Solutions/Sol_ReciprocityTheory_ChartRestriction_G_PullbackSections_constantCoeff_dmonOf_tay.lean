-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.constantCoeff_dmonOf_tay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:47.931264+00:00
-- url     : https://prove2.me/submissions/b45b5116-6aac-4094-ae89-6e787a19d067

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_foldr_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_toMultiset_map_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_constantCoeff_tay

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
    (u : ι → Fin g → ℂ) (m : ι →₀ ℕ) :
    constantCoeff (DmonOf (addF ℂ g) u m (tay θ 0)) = mD θ 0 ((Finsupp.toMultiset m).map u) := by
  unfold DmonOf
  rw [foldr_tay hθ, add_zero, constantCoeff_tay, toMultiset_map_eq]
  congr 1
  first
  | exact Finset.sum_toList _ _
  | exact Finset.sum_to_list _ _
  | simp [Finset.sum_toList]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
