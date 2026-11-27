-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.not_dim_strict_lt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:45.454323+00:00
-- url     : https://prove2.me/submissions/2059469d-7a82-47cc-9fc8-45bc8ba8a8b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x y : WithBot ℕ∞} {D : ℕ} (hx : x = ((D + 2 : ℕ) : WithBot ℕ∞))
    (h : x + 1 ≤ y) (hy : y ≤ ((D + 2 : ℕ) : WithBot ℕ∞)) : False := by
  subst hx
  have := h.trans hy
  have h' : (((D + 2 + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((D + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast this
  have h'' : D + 2 + 1 ≤ D + 2 := by exact_mod_cast h'
  omega
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
