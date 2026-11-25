-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.mA_chiP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:07.1074+00:00
-- url     : https://prove2.me/submissions/4b95b9f0-64ce-4584-8bce-54379932b71c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ActActA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_mA_fst

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
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e)
    (hta : TorusEndOf D.toPre.X (fun χ => star a • χ) ta) (χ : D.toPre.X)
    (W2 W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hm : W' ≤ (mA ιG e a ta).left ⁻¹ᵁ W2) :
    ((mA ιG e a ta).left.appLE W2 W' hm).hom
        (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
          (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) χ)) =
      ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) := by
  have hF : (mA ιG e a ta).left ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left =
      (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ ta.left := by
    rw [← Over.comp_left, mA_fst, Over.comp_left]
  have hTop : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫
      (mA ιG e a ta).left.appTop =
      ta.left.appTop ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop := by
    rw [← Scheme.Hom.comp_appTop, hF, Scheme.Hom.comp_appTop]
  have hval := congrArg Units.val (hta χ)
  simp only [Semi.res, Semi.pullU, Units.coe_map, MonoidHom.coe_coe] at hval
  simp only [Semi.TorusInj.chiP, ← hval]
  simp only [Scheme.Hom.appLE]
  have hTop' : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫ (mA ιG e a ta).left.app ⊤ = ta.left.app ⊤ ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.app ⊤ := hTop

  have key : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W2 ≤ ⊤)).op ≫
      (mA ιG e a ta).left.app W2 ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE hm).op =
      ta.left.app ⊤ ≫
      (WeightPf.Te D.toPre I e).left.presheaf.map
        (homOfLE (fun _ _ => trivial : (⊤ : (WeightPf.Te D.toPre I e).left.Opens) ≤ ta.left ⁻¹ᵁ ⊤)).op ≫
      (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.app ⊤ ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (fun _ _ => trivial : W' ≤ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ ⊤)).op := by
    rw [Scheme.Hom.naturality_assoc, Scheme.Hom.naturality_assoc, reassoc_of% hTop']
    simp only [← Functor.map_comp]
    rfl
  have hk := congrArg (fun φ => φ.hom (charUnit _ D.toPre.X χ).val) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hk ⊢
  exact hk
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
