-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.iterate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:56:21.852923+00:00
-- url     : https://prove2.me/submissions/dc233a35-55ed-4e60-88c6-0c3386f1ce11

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_degLt_iterate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_eq_zero_of_degLt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_degLt_totalDegree

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
theorem _root_.solution (c : ι → ι → k) (P : MvPolynomial ι k) :
    (secondOrder k c)^[P.totalDegree + 1] P = 0 :=
  eq_zero_of_degLt_zero (degLt_iterate c 0 _ (by rw [Nat.zero_add]; exact degLt_totalDegree P))
end ReciprocityTheory.ChartRestriction.G.TB.GE
