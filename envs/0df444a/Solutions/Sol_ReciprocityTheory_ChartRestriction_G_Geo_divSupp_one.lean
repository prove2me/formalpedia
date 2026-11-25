-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.divSupp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:14.01752+00:00
-- url     : https://prove2.me/submissions/c08a11ab-d892-4af5-9396-e26e6b4cc5b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P : Ideal (MRing ι)) : divSupp P 1 = ∅ := by
  ext W
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hW
  have hp := hW.1
  have htop : (⊤ : Ideal (MRing ι)) ≤ W := by
    have h2 := hp.2
    rwa [Ideal.span_singleton_one, sup_top_eq] at h2
  exact fun _ => hp.1.ne_top (top_le_iff.1 htop)
end ReciprocityTheory.ChartRestriction.G.Geo
