-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I2.IsIntersectionFamily.isRFamily
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:04.647167+00:00
-- url     : https://prove2.me/submissions/e69cb41f-8294-4292-b675-74b06dd5869d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.AI.I2
namespace IsIntersectionFamily
theorem _root_.solution {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (h : IsIntersectionFamily I) : IsRFamily I :=
  h.2
end IsIntersectionFamily
end ReciprocityTheory.ChartRestriction.G.AI.I2
