-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:49.441968+00:00
-- url     : https://prove2.me/submissions/9fb9912e-b867-4b26-9dcd-e985ee41263d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {n : ℕ} {a : Pt k n d} (ha : GP a) : ∀ j, GP (![a] j) := by
  intro j
  first
    | (rw [Matrix.cons_val_fin_one]; exact ha)
    | (fin_cases j; exact ha)
    | (fin_cases j; simpa using ha)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
