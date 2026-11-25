-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.eSec_face
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:09.556979+00:00
-- url     : https://prove2.me/submissions/7064f704-6a44-4c64-9818-e4d69438cce0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExtVCat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_eta_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_one_comp_proj_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_lift_one_one

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (i : Fin 3) : eSec (G2 G) ≫ (faceMap G i).left = eSec (G3 G) := by
  show (η[G2 G]).left ≫ (faceMap G i).left = (η[G3 G]).left
  rw [← Over.comp_left, eta_eq_one, eta_eq_one]
  congr 1
  have hp : (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ pzero G (G2 G) = 1 := by
    rw [pzero, ← Category.assoc, toUnit_unique ((1 : 𝟙_ (Over S) ⟶ G2 G) ≫ toUnit _) (toUnit _)]; rfl
  fin_cases i
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (pzero G _) (lift (x2 G 0) (x2 G 1)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (x2 G 0) (lift (pzero G _) (x2 G 1)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]
  · show (1 : 𝟙_ (Over S) ⟶ G2 G) ≫ lift (x2 G 0) (lift (x2 G 1) (pzero G _)) = 1
    rw [comp_lift, comp_lift, hp, one_comp_proj_two, one_comp_proj_two, lift_one_one]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
