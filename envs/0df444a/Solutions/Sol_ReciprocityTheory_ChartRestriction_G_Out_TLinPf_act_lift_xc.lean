-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.act_lift_xc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:50.829808+00:00
-- url     : https://prove2.me/submissions/139ab10b-bbad-417f-8495-ada5593bc9a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_q

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
section SlopeTestRemainingChoices
variable {Y Z : Scheme.{0}} (L : LB Y) {K K' : Type} [Fintype K] [Fintype K']
end SlopeTestRemainingChoices
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
private lemma pG_act_lemma :
    (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫ (U.gt e).pG =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫
        (U.gt e).pG := by
  first
    | (simp only [GtCoord.pG]
       rw [← Category.assoc, ← Functor.map_comp, WeightPf.act_q, Functor.map_comp, Category.assoc])
    | simp [GtCoord.pG, ← Functor.map_comp_assoc, WeightPf.act_q]
private lemma unit_act_lemma :
    (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫
        toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫
        toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) :=
  toUnit_unique _ _
private lemma left_act_lemma {A' : Over (Spec (CommRingCat.of R))}
    (p : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ A')
    (hp : (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫ p =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫ p) :
    (WeightPf.act (U.gt e)).left ≫ p.left =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ p.left := by
  simpa using congrArg CommaMorphism.left hp
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution :
    (WeightPf.act (U.gt e)).left ≫ (lift (xc e χ (G := G)) (U.gt e).pG).left =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
        (lift (xc e χ (G := G)) (U.gt e).pG).left := by
  refine left_act_lemma (U := U) (e := e) _ ?_
  first
    | (rw [comp_lift, comp_lift, pG_act_lemma]
       simp only [xc, ← Category.assoc, unit_act_lemma])
    | simp [xc, pG_act_lemma, unit_act_lemma]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
