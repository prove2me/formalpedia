-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.bm_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:00:55.951257+00:00
-- url     : https://prove2.me/submissions/fb1112e1-542c-441a-bff6-64b3b6615813

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_iB_h


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] {G : Over S} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution (i : splitTorus S X ⟶ G) :
    (lift (fst (splitTorus S' X) ((Over.pullback f).obj G) ≫ iB f X i)
        (snd (splitTorus S' X) ((Over.pullback f).obj G)) ≫ μ[(Over.pullback f).obj G]).left ≫
      pullback.fst G.hom f =
    bm f X ≫ (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left := by
  have hx : (lift (uT f X) (vG f X) ≫ fst (splitTorus S X) G ≫ i).left =
      (fst (splitTorus S' X) ((Over.pullback f).obj G) ≫ iB f X i).left ≫ pullback.fst G.hom f := by
    rw [← Category.assoc, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, iB_h]
    exact Category.assoc _ _ _
  have hy : (lift (uT f X) (vG f X) ≫ snd (splitTorus S X) G).left =
      (snd (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f := by
    rw [lift_snd]
    rfl
  have key := (isGrpPullback_pullback G f).2 _ _ _ _ _ hx hy
  rw [← Hom.mul_def, ← Hom.mul_def, ← key, ← MonObj.comp_mul]
  rfl
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
