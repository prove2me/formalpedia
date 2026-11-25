-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pushR_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:00:44.05478+00:00
-- url     : https://prove2.me/submissions/72dbb580-7a49-4715-857a-8977f2a1b5a1

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
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {d : ℕ} (v : Fin d → (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G)) :
    pushR G (List.ofFn v).prod = (List.ofFn fun i => pushR G (v i)).prod := by
  have h := map_list_prod (pushforwardHom (R := R) (R' := R') (P := P) G) (List.ofFn v)
  rw [List.map_ofFn] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.Chart
