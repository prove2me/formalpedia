-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.T_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:08.35116+00:00
-- url     : https://prove2.me/submissions/615201be-89e1-4b4b-b83e-1406149136d2

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
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (l : ι) (w : List ι) (A : PS k 1 d) : T F u (l :: w) A = Dof F (u l) (T F u w A) := rfl
end ReciprocityTheory.ChartRestriction.G.TB.G2
