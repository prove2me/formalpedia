-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_span_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:16.28793+00:00
-- url     : https://prove2.me/submissions/b767adb2-0abf-4abd-b319-7ec9e0d80cd4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_X

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
    (q : Σ k, ι k) : IsMultiHomogIdeal (Ideal.span {(X q : MRing ι)}) := by
  refine ⟨{X q}, ?_, rfl⟩
  rintro f rfl
  exact ⟨_, isMultiHomog_X q⟩
end ReciprocityTheory.ChartRestriction.G.Geo
