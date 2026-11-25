-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.finsum_dimOne_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:10.692425+00:00
-- url     : https://prove2.me/submissions/83ca58b9-382e-4666-9498-581b9d99ef37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (hdim : ringKrullDim A = 1) (F : PrimeSpectrum A → ℕ∞) :
    ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1), F p =
      ∑ p ∈ (finite_dimOne hdim).toFinset, F p := by
  exact finsum_mem_eq_finite_toFinset_sum F (finite_dimOne hdim)
end ReciprocityTheory.ChartRestriction.G.AI
