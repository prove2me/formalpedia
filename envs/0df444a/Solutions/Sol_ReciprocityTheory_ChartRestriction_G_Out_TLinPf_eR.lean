-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.eR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:03.391231+00:00
-- url     : https://prove2.me/submissions/233c0f86-f84c-4b41-a219-533b4c71df96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero

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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
variable {U ιD e a χ}
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution (f g : D.toPre.P.A ⟶ D.toPre.P.A) (X P : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.toPre.P.A) :
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 0 = (padd D.toPre.P.A (X ≫ f) P).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 1 = (X ≫ f).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 2 = P.left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 3 = (padd D.toPre.P.A X (P ≫ g)).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 4 = X.left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 5 = (P ≫ g).left := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (lift X P).left ≫ (padd D.toPre.P.A (fst D.toPre.P.A D.toPre.P.A ≫ f) (snd D.toPre.P.A D.toPre.P.A)).left = _
    rw [← Over.comp_left]
    congr 1
    simp only [padd]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    simp
  · change (lift X P).left ≫ (fst D.toPre.P.A D.toPre.P.A ≫ f).left = _
    rw [← Over.comp_left]
    congr 1
    simp
  · change (lift X P).left ≫ (snd D.toPre.P.A D.toPre.P.A).left = _
    rw [← Over.comp_left]
    congr 1
    simp
  · change (lift X P).left ≫ (padd D.toPre.P.A (fst D.toPre.P.A D.toPre.P.A) (snd D.toPre.P.A D.toPre.P.A ≫ g)).left = _
    rw [← Over.comp_left]
    congr 1
    simp only [padd]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    simp
  · change (lift X P).left ≫ (fst D.toPre.P.A D.toPre.P.A).left = _
    rw [← Over.comp_left]
    congr 1
    simp
  · change (lift X P).left ≫ (snd D.toPre.P.A D.toPre.P.A ≫ g).left = _
    rw [← Over.comp_left]
    congr 1
    simp
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
