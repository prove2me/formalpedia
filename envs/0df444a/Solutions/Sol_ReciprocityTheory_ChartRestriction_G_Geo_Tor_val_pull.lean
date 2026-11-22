-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:19.585611+00:00
-- url     : https://prove2.me/submissions/ee11e3bd-afa1-44ef-a8e1-6bd720655f55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Y' Z : Scheme.{0}}
variable (L : LB X)
variable {L} {K K' : Type} [Fintype K] [Fintype K']
variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') :
    val (LB.pullGen L φ ε t h) r z J = val t (r ≫ h) z J := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  simp only [val, LB.pullGen]
  have hm : h (r z) ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gm_res r z _ (hJ.mem (fun k => h ≫ φ k) r) _).trans (gm_pull r h z _ hm _)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
