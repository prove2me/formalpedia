-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.eSec_pG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:29.586297+00:00
-- url     : https://prove2.me/submissions/7302c34b-6661-4e13-a4bb-ac194346f84d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
theorem _root_.solution : (Over.map (thick R I e)).map η[thickObj R I e G] ≫ (U.gt e).pG =
    toUnit _ ≫ η[D.toPre.P.A] := by
  have := (U.gt e).q_hom
  ext1
  have h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A] := IsMonHom.one_hom _
  have h2 := congrArg Over.Hom.left h1
  simp only [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left] at h2 ⊢
  rw [← Category.assoc, h2, Functor.obj.η_def]
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  have h3 := Over.w (toUnit ((Over.map (thick R I e)).obj (𝟙_ _)))
  have h4 := Over.w (Functor.LaxMonoidal.ε (Over.pullback (thick R I e)))
  have h5 := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of R)))).hom) (g := thick R I e)
  simp only [Over.map_obj_hom, Functor.id_obj, Over.pullback_obj_hom] at h3 h4 h5
  have h5' : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) =
      pullback.snd (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) ≫ thick R I e :=
    (Category.comp_id _).symm.trans h5
  have h3' : Over.Hom.left (toUnit ((Over.map (thick R I e)).obj
      (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))))) = thick R I e :=
    (Category.comp_id _).symm.trans (h3.trans (Category.id_comp _))
  have key : Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback (thick R I e))) ≫
      pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) =
      Over.Hom.left (toUnit ((Over.map (thick R I e)).obj
        (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))))) := by
    rw [h5', ← Category.assoc, h4, h3']
    exact Category.id_comp _
  rw [← Category.assoc, key]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
