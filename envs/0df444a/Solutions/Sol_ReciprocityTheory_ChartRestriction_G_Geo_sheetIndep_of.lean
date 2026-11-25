-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:51.946708+00:00
-- url     : https://prove2.me/submissions/7bf2d109-fa89-45bc-b055-fcdc3ab614c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_density_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sheet_analyticAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_badSet_null


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
open MeasureTheory Metric Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (hA : OsgoodStatement) (hfib : FibreFiniteStatement) : SheetIndepStatement := by
  intro K _ ι _ P e Ψ L A s hvar hgood hL _ hs
  have hbad := badSet_null hA (hfib K ι P e Ψ hvar hgood)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbad] with y hy w γ γ' h h'
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y') := by
    by_contra hne
    exact hy ⟨w, γ, γ', h, h', hne⟩
  exact density_eq hL hs (sheet_analyticAt hA h) (sheet_analyticAt hA h') h.2.self_of_nhds.2.1.1 hseg
end ReciprocityTheory.ChartRestriction.G.Geo
