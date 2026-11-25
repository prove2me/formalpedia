-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.polyDeriv_eq_mD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:28:02.1949+00:00
-- url     : https://prove2.me/submissions/526015be-cbf4-43dc-a97a-c16f3268dd24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_lD_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_mD_coe

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
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} (P : MvPolynomial ι ℂ)
    (u : ι → Fin g → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u θ 0 =
      ∑ m ∈ P.support, P.coeff m * mD θ 0 ((Finsupp.toMultiset m).map u) := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hL : (Finsupp.toMultiset m).map u =
      (((Finsupp.toMultiset m).toList.map u : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  have hlen : ((Finsupp.toMultiset m).toList.map u).length = Multiset.card (Finsupp.toMultiset m) := by
    rw [List.length_map, Multiset.length_toList]
  rw [hL, mD_coe hθ, lD_eq θ 0 _ hlen]
  congr 1
  funext k
  simp [List.get_eq_getElem]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
