-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.eq_zero_of_degLt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:24.241372+00:00
-- url     : https://prove2.me/submissions/9e2af607-1276-4ca8-bbc2-464011ba8dec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution {P : MvPolynomial ι k} (h : DegLt 0 P) : P = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  exact h m (Nat.zero_le _)
end ReciprocityTheory.ChartRestriction.G.TB.GE
