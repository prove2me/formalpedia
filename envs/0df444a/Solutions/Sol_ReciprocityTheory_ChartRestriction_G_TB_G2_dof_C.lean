-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.dof_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:39.449493+00:00
-- url     : https://prove2.me/submissions/d4cb2128-b419-49d3-bf46-04baa0f0b465

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) (v : Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (a : k) : Dof F v (C a : PS k 1 d) = 0 := by
  unfold Dof
  have h : ∀ j : Fin d, pderiv k ((0 : Fin 1), j) (C a : PS k 1 d) = 0 := fun j => by
    simp
  simp [h]
end ReciprocityTheory.ChartRestriction.G.TB.G2
