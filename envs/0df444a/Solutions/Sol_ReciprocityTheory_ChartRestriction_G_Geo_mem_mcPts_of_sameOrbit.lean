-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.mem_mcPts_of_sameOrbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:29.748654+00:00
-- url     : https://prove2.me/submissions/05585c5f-c35c-4340-999a-7f39904d8518

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul

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
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (hz' : z' ∈ mcPts J) : z ∈ mcPts J := by
  obtain ⟨c, hc, rfl⟩ := h
  exact mcPts_smul hJ c hc hz'
end ReciprocityTheory.ChartRestriction.G.Geo
