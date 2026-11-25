-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.degLt_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:24.447132+00:00
-- url     : https://prove2.me/submissions/97420d52-53d9-47f3-b6b8-8328c7713e8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_degLt_secondOrder

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
theorem _root_.solution (c : ι → ι → k) (n j : ℕ) {P : MvPolynomial ι k} (h : DegLt (n + j) P) :
    DegLt n ((secondOrder k c)^[j] P) := by
  induction j generalizing P with
  | zero => first | exact h | simpa using h
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (degLt_secondOrder c (n := n + j) (by first | exact h | simpa [Nat.add_assoc] using h))
end ReciprocityTheory.ChartRestriction.G.TB.GE
