-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:32.962024+00:00
-- url     : https://prove2.me/submissions/67975c56-b903-4744-b24d-ff6e037a7b0e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed

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
open MvPolynomial ReciprocityTheory.AnForm.M
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) :
    IsMultiHomog (X q : MRing ι) (fun k => ∑ i, (Finsupp.single q 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩) := by
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo
