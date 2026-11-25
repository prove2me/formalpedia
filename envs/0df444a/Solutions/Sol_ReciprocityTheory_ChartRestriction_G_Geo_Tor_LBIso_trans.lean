-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:09.490261+00:00
-- url     : https://prove2.me/submissions/a1504774-7ba3-45d8-b272-afe6eb23e07f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_chartPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X Y Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace LBIso
theorem _root_.solution {A B C : LB X} (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) (H : LBIso A B) (H' : LBIso B C) :
    LBIso A C := by
  obtain ⟨w', h'⟩ := H.chartPull (chartPullId A) (chartPullPull B (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w, h⟩ := H'.chartPull (chartPullId B) (chartPullPull C (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w'', T⟩ := exists_comp hB w w' ((isGen_iff w).1 h) ((isGen_iff w').1 h') hC hA
  exact LBIso.chartPull (chartPullId A) (chartPullUnpull C _ (Category.id_comp _))
    ⟨w'', (isGen_iff w'').2 (T.pgen_comp hB ((isGen_iff w).1 h) ((isGen_iff w').1 h'))⟩
end LBIso
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
