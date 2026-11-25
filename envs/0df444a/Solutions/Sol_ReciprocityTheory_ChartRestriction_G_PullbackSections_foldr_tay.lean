-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.foldr_tay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:59.675856+00:00
-- url     : https://prove2.me/submissions/b1bbb71a-14dd-428e-bb31-07319c89aafd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_dof_iter_tay

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
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} (u : ι → Fin g → ℂ)
    (m : ι →₀ ℕ) (L : List ι) (s : Multiset (Fin g → ℂ)) :
    L.foldr (fun l f => (Dof (addF ℂ g) (u l))^[m l] f) (tay θ s) =
      tay θ ((L.map fun l => Multiset.replicate (m l) (u l)).sum + s) := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.foldr_cons, ih, dof_iter_tay hθ, List.map_cons, List.sum_cons, add_assoc]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
