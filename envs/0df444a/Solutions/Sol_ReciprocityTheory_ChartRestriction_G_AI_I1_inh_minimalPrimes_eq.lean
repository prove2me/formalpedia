-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_minimalPrimes_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:29.384427+00:00
-- url     : https://prove2.me/submissions/276847b2-0cbb-4989-bc64-23b0dfa56101

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
theorem _root_.solution {I Q : Ideal R} [hQ : Q.IsPrime] (hIQ : I ≤ Q)
    (hmin : ∀ q : Ideal R, q.IsPrime → I ≤ q → Q ≤ q) : I.minimalPrimes = {Q} := by
  ext W
  simp only [Ideal.minimalPrimes, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact le_antisymm (h.2 ⟨hQ, hIQ⟩ (hmin W h.1.1 h.1.2)) (hmin W h.1.1 h.1.2)
  · rintro rfl
    exact ⟨⟨hQ, hIQ⟩, fun y hy _ => hmin y hy.1 hy.2⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
