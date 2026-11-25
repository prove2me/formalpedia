-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.lamW_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:21.31948+00:00
-- url     : https://prove2.me/submissions/c8831e86-a9fa-47d3-a954-981bb768b0ea

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
theorem _root_.solution (n : ι →₀ ℕ) (a : k) :
    lamW ψ (MvPolynomial.monomial n a) = a * ψ (word (Finset.univ : Finset ι).toList n) := by
  show (Finsupp.single n a).sum _ = _
  exact Finsupp.sum_single_index (zero_mul _)
end ReciprocityTheory.ChartRestriction.G.TB.G2
