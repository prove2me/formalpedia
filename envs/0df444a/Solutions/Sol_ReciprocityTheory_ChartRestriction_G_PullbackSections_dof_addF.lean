-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.dof_addF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:02.057614+00:00
-- url     : https://prove2.me/submissions/c210b47e-2647-4b4c-b125-a32795ce2455

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_ev_zero__ee2e67940270

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
variable (R : Type) [CommRing R]
variable {R}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {g : ℕ} (v : Fin g → R) (f : PS R 1 g) :
    Dof (addF R g) v f = ∑ j, C (v j) * pderiv R ((0 : Fin 1), j) f := by
  classical
  unfold Dof
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply]
  · intro b _ hb
    simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply, hb, Ne.symm hb, ev_zero']
  · intro h
    exact absurd (Finset.mem_univ j) h
end ReciprocityTheory.ChartRestriction.G.PullbackSections
