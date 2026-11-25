-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.lift_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:50.518286+00:00
-- url     : https://prove2.me/submissions/7feb3e63-8fb1-48d5-9c9c-ae12269baf7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_mcPts_of_sameOrbit


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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {x z : R.X} (hz : z ∈ R.U x) :
    R.lift z z ∈ mcPts J ↔ R.lift x z ∈ mcPts J := by
  have h1 : SameOrbit (R.lift z z) (R.lift x z) := R.compat z x z ⟨R.mem_U z, hz⟩
  have h2 : SameOrbit (R.lift x z) (R.lift z z) := R.compat x z z ⟨hz, R.mem_U z⟩
  exact ⟨mem_mcPts_of_sameOrbit R.homog h2, mem_mcPts_of_sameOrbit R.homog h1⟩
end ReciprocityTheory.ChartRestriction.G.Geo
