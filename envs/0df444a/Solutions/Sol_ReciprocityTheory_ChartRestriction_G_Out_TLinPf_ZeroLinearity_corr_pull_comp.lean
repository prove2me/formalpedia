-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.corr_pull_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:17:29.556669+00:00
-- url     : https://prove2.me/submissions/41be1b44-be44-4a45-bb9f-e916fc433f50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_pullGen_s_val
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
private lemma appLE_appLE_lemma_2 {B T : W.Opens} {C : Y.Opens} {D : Z.Opens} (g1 : Z ⟶ Y)
    (g2 : W ⟶ Z) (e1 : D ≤ g1 ⁻¹ᵁ C) (e2 : B ≤ g2 ⁻¹ᵁ D) (hT : T ≤ B) (x : Γ(Y, C)) :
    (W.presheaf.map (homOfLE hT).op).hom ((g2.appLE D B e2).hom ((g1.appLE C D e1).hom x)) =
      ((g2 ≫ g1).appLE C T (hT.trans (e2.trans (g2.preimage_mono e1)))).hom x := by
  change (g1.app C ≫ Z.presheaf.map (homOfLE e1).op ≫ g2.appLE D B e2 ≫
    W.presheaf.map (homOfLE hT).op).hom x = _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  first
  | rfl
  | simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]
  | simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]
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
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb L φ ε)) (g1 : Z ⟶ Y)
    (g2 : W ⟶ Z) (g : W ⟶ Y) (hg : g2 ≫ g1 = g) :
    LB.Gen.Corr L _ ε _ ε (LB.pullGen L _ ε (LB.pullGen L φ ε c g1) g2) (LB.pullGen L φ ε c g) := by
  subst hg
  intro j j' _ _ hjj
  obtain rfl : j = j' := funext fun k => hjj k k (by simp)
  ext
  change (W.presheaf.map (homOfLE _).op).hom
      ((LB.pullGen L _ ε (LB.pullGen L φ ε c g1) g2).s j).val =
    (W.presheaf.map (homOfLE _).op).hom ((LB.pullGen L φ ε c (g2 ≫ g1)).s j).val
  rw [pullGen_s_val, pullGen_s_val, pullGen_s_val]
  exact (appLE_appLE_lemma_2 g1 g2 _ _ _ _).trans (appLE_res_lemma_3 (g2 ≫ g1) _ _ _).symm
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
