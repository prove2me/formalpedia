-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pre_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:01.334347+00:00
-- url     : https://prove2.me/submissions/ba2c75b8-5d54-418d-a501-3d09810da58b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) {d : ℕ} (v : Fin d → (X ⟶ M)) :
    f ≫ (List.ofFn v).prod = (List.ofFn fun i => f ≫ v i).prod := by
  have h := map_list_prod (preH (M := M) f) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.Chart
