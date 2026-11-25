-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.lam_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:48.957265+00:00
-- url     : https://prove2.me/submissions/8c676b1c-3c4f-4486-9431-94f7ea621e10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull

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
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
variable {k : Type} [CommRing k] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (W : (σ →₀ ℕ) → k) (m : σ →₀ ℕ) (r : k) : lam W (monomial m r) = r * W m := by
  classical
  rw [lam_eq W _ {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
