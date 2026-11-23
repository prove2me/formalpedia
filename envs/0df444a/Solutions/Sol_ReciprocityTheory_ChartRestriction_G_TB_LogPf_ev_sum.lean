-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:06.848571+00:00
-- url     : https://prove2.me/submissions/c1328da8-7cc5-44e6-9f35-75a0e44b1e9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_evHom_apply

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d m n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution {a : Fin m → Pt k n d} (ha : CZ a) {ι : Type} (s : Finset ι) (f : ι → PS k m d) :
    ev a (∑ x ∈ s, f x) = ∑ x ∈ s, ev a (f x) := by
  rw [← evHom_apply ha, map_sum]
  exact Finset.sum_congr rfl (fun x _ => evHom_apply ha (f x))
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
