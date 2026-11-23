-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.hasSubst_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:17.191526+00:00
-- url     : https://prove2.me/submissions/707ee0bd-2256-4109-a6c6-f0ab9b304f4c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
variable {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt k n d} (ha : ∀ p q, constantCoeff (a p q) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero fun p => ha p.1 p.2
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
