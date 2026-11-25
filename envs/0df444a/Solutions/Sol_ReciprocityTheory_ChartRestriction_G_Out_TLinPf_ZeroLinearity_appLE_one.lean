-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.appLE_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:35:11.804112+00:00
-- url     : https://prove2.me/submissions/3e6ddfd9-03df-4851-b44d-cb1178e33983

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_pullGen_s_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_corr_one_alt
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
namespace ZeroLinearity
section SlopeTestRemainingChoices
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
private lemma appLE_res_lemma_3 (f : W ⟶ Y) {C : Y.Opens} {B T : W.Opens} (e : B ≤ f ⁻¹ᵁ C)
    (hT : T ≤ B) (x : Γ(Y, C)) :
    (W.presheaf.map (homOfLE hT).op).hom ((f.appLE C B e).hom x) = (f.appLE C T (hT.trans e)).hom x := by
  change (f.appLE C B e ≫ W.presheaf.map (homOfLE hT).op).hom x = _
  rw [Scheme.Hom.appLE_map]
end SlopeTestRemainingChoices
section Z
variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (f g : B ⟶ B) [IsMonHom g]
end Z
section Unit
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)
end Unit
end ZeroLinearity
open ZeroLinearity
section Main
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
end Main
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
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hC : LB.Gen.Corr L _ ε PEmpty.elim PEmpty.elim (LB.pullGen L φ ε t h) (LB.oneGen L))
    (j : K → L.ι) (hj : LB.Coh L (fun k => h ≫ φ k) j) (V : Z.Opens)
    (hV : V ≤ LB.wchart L (fun k => h ≫ φ k) j) :
    (h.appLE (LB.wchart L φ j) V (hV.trans (LBVal.wchart_pull_le L φ h j))).hom (t.s j).val = 1 := by
  have e2 := congrArg Units.val (corr_one_alt L hC j hj)
  rw [pullGen_s_val, Units.val_one] at e2
  exact (appLE_res_lemma_3 h (LBVal.wchart_pull_le L φ h j) hV _).symm.trans
    ((congrArg (fun y => (Z.presheaf.map (homOfLE hV).op).hom y) e2).trans (map_one _))
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
