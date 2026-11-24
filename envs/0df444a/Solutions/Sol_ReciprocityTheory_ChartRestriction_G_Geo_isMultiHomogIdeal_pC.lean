-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_pC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:22.515769+00:00
-- url     : https://prove2.me/submissions/bafd6e61-1682-4e19-b396-4f5d0f1e44e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor

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
open MvPolynomial MultiHomogZ
open scoped Pointwise
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨map (Int.castRingHom ℂ) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · exact Ideal.map_span (map (Int.castRingHom ℂ)) S
end ReciprocityTheory.ChartRestriction.G.Geo
