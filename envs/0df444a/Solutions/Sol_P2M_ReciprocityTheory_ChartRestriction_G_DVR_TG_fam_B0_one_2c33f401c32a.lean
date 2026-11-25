-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_one_2c33f401c32a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:58.832125+00:00
-- url     : https://prove2.me/submissions/c11d8088-653f-4a35-a4ee-0378d27d9785

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenRank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_c_zero

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I)
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution : D.toPre.famφB 0 1 = 𝟙 _ := by
  have h1 : (toUnit D.toPre.P.A ≫ D.toPre.c 0) = 1 := by
    rw [c_zero D]
    first
    | simp [Hom.one_def]
    | (rw [Hom.one_def, Hom.one_def, ← Category.assoc]; congr 1)
  show (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = 𝟙 _
  rw [h1]
  show ((𝟙 D.toPre.P.A) * 1 : D.toPre.P.A ⟶ D.toPre.P.A).left = _
  rw [_root_.mul_one]
  first
  | rfl
  | simp
end ReciprocityTheory.ChartRestriction.G.DVR.TG
