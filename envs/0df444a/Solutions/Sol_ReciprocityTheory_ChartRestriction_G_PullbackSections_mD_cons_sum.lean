-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.mD_cons_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:01.57701+00:00
-- url     : https://prove2.me/submissions/24ae8173-237f-40eb-84fc-d5919f5677f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_mD_cons

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) {ι : Type} (t : Finset ι) (c : ι → ℂ)
    (w : ι → V) (s : Multiset V) :
    mD φ x ((∑ i ∈ t, c i • w i) ::ₘ s) = ∑ i ∈ t, c i * mD φ x (w i ::ₘ s) := by
  simp only [mD_cons hφ, map_sum, map_smul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
