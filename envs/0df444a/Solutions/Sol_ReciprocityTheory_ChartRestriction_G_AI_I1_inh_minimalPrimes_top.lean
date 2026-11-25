-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_minimalPrimes_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:31.766538+00:00
-- url     : https://prove2.me/submissions/a39cddad-fd5d-4d3c-a117-048d3a5c5872

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution : (⊤ : Ideal R).minimalPrimes = ∅ := by
  ext W
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨⟨hp, hle⟩, -⟩ := h
  exact hp.ne_top (top_le_iff.mp hle)
end ReciprocityTheory.ChartRestriction.G.AI.I1
