-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.secondOrder_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:26.981603+00:00
-- url     : https://prove2.me/submissions/0999ceba-7e05-4045-b3bb-7eef846b7e50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (c : ι → ι → k) (p q : MvPolynomial ι k) :
    secondOrder k c (p + q) = secondOrder k c p + secondOrder k c q := by
  unfold secondOrder
  simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib]
  done
end ReciprocityTheory.ChartRestriction.G.TB.G2
