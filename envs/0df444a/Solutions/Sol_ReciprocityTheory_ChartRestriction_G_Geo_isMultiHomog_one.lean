-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:05.302825+00:00
-- url     : https://prove2.me/submissions/2a9d579e-67d7-4b5a-a67b-a9aea9256021

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
theorem _root_.solution : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  simp
end ReciprocityTheory.ChartRestriction.G.Geo
