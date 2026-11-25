-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.dof_iter_tay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:55:37.475837+00:00
-- url     : https://prove2.me/submissions/8ea1f9ff-6c4c-4514-876d-f60549a0a63e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_dof_tay

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
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (k : ℕ)
    (s : Multiset (Fin g → ℂ)) :
    (Dof (addF ℂ g) v)^[k] (tay θ s) = tay θ (Multiset.replicate k v + s) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, dof_tay hθ, Multiset.replicate_succ, Multiset.cons_add]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
