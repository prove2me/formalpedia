-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.lhs_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:45:59.871145+00:00
-- url     : https://prove2.me/submissions/d1c53612-54a9-4fb8-94e7-c827d80b7fd6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_appLE_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_appLE_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_act_lift_xc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_hA_act
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
private lemma res_val_lemma {X₀ : Scheme.{0}} {U₀ V₀ W₀ : X₀.Opens} (e₀ : V₀ ≤ U₀) (hW : W₀ ≤ V₀)
    (x : Γ(X₀, U₀)ˣ) :
    (X₀.presheaf.map (homOfLE hW).op).hom (res e₀ x).val =
      (X₀.presheaf.map (homOfLE (hW.trans e₀)).op).hom x.val := by
  show (X₀.presheaf.map (homOfLE e₀).op ≫ X₀.presheaf.map (homOfLE hW).op).hom x.val = _
  rw [← Functor.map_comp]
  rfl
private lemma pull_val_lemma {X₀ Y₀ : Scheme.{0}} (g : Y₀ ⟶ X₀) (U₀ : X₀.Opens) {W₀ : Y₀.Opens}
    (hW : W₀ ≤ g ⁻¹ᵁ U₀) (x : Γ(X₀, U₀)ˣ) :
    (Y₀.presheaf.map (homOfLE hW).op).hom (pullU g U₀ x).val = (g.appLE U₀ W₀ hW).hom x.val :=
  rfl
private lemma corr_val_lemma {X₀ : Scheme.{0}} {V₀ V₁ V₂ W₀ : X₀.Opens} (h₁ : V₀ ≤ V₁) (h₂ : V₀ ≤ V₂)
    (x : Γ(X₀, V₁)ˣ) (y : Γ(X₀, V₂)ˣ) (hE : res h₁ x = res h₂ y) (hW₁ : W₀ ≤ V₁) (hW₂ : W₀ ≤ V₂)
    (hW : W₀ ≤ V₀) :
    (X₀.presheaf.map (homOfLE hW₁).op).hom x.val = (X₀.presheaf.map (homOfLE hW₂).op).hom y.val := by
  have h3 := congrArg (fun z => (X₀.presheaf.map (homOfLE hW).op).hom (Units.val z)) hE
  simp only [res_val_lemma] at h3
  exact h3
private lemma mulGen_val_lemma {X₀ Y₀ : Scheme.{0}} (L₀ : LB X₀) {K₀ K₁ : Type} [Fintype K₀]
    [Fintype K₁] (φ : K₀ → (Y₀ ⟶ X₀)) (ε : K₀ → ℤ) (φ' : K₁ → (Y₀ ⟶ X₀)) (ε' : K₁ → ℤ)
    (t : LB.Gen (LB.LinComb L₀ φ ε)) (t' : LB.Gen (LB.LinComb L₀ φ' ε')) (j : K₀ ⊕ K₁ → L₀.ι)
    {W₀ : Y₀.Opens} (hW : W₀ ≤ LB.wchart L₀ (Sum.elim φ φ') j) :
    (Y₀.presheaf.map (homOfLE hW).op).hom ((LB.mulGen L₀ φ ε φ' ε' t t').s j).val =
      (Y₀.presheaf.map (homOfLE (hW.trans (wchart_inl_le L₀ φ φ' j))).op).hom
          (t.s (j ∘ Sum.inl)).val *
        (Y₀.presheaf.map (homOfLE (hW.trans (wchart_inr_le L₀ φ φ' j))).op).hom
          (t'.s (j ∘ Sum.inr)).val := by
  simp only [LB.mulGen, Units.val_mul, map_mul]
  congr 1 <;> exact res_val_lemma _ _ _
private lemma pullGen_val_lemma {X₀ Y₀ Z₀ : Scheme.{0}} (L₀ : LB X₀) {K₀ : Type} [Fintype K₀]
    (φ : K₀ → (Y₀ ⟶ X₀)) (ε : K₀ → ℤ) (c : LB.Gen (LB.LinComb L₀ φ ε)) (h : Z₀ ⟶ Y₀)
    (j : K₀ → L₀.ι) {W₀ : Z₀.Opens} (hW : W₀ ≤ LB.wchart L₀ (fun k => h ≫ φ k) j) :
    (Z₀.presheaf.map (homOfLE hW).op).hom ((LB.pullGen L₀ φ ε c h).s j).val =
      (h.appLE (LB.wchart L₀ φ j) W₀ (hW.trans (Semi.LBVal.wchart_pull_le L₀ φ h j))).hom
        (c.s j).val :=
  (res_val_lemma _ _ _).trans (pull_val_lemma _ _ _ _)
private lemma charGen_val_lemma {S₀ : Scheme.{0}} (X₁ : Type) [AddCommGroup X₁] (G₀ : Over S₀)
    {Z₀ : Scheme.{0}} (L₀ : LB Z₀) (χ₀ : X₁) (j : PEmpty → L₀.ι)
    {W₀ : (splitTorus S₀ X₁ ⊗ G₀).left.Opens}
    (hW : W₀ ≤ LB.wchart L₀ (Y := (splitTorus S₀ X₁ ⊗ G₀).left) (K := PEmpty) PEmpty.elim j) :
    ((splitTorus S₀ X₁ ⊗ G₀).left.presheaf.map (homOfLE hW).op).hom
        ((charGen X₁ G₀ L₀ χ₀).s j).val =
      ((splitTorus S₀ X₁ ⊗ G₀).left.presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op).hom
        (Semi.TorusInj.chiP X₁ G₀ χ₀) :=
  (res_val_lemma _ _ _).trans rfl
private lemma appLE_congr_lemma {X₀ Y₀ : Scheme.{0}} {f g : Y₀ ⟶ X₀} (hfg : f = g) {U₀ : X₀.Opens}
    {W₀ : Y₀.Opens} (h₁ : W₀ ≤ f ⁻¹ᵁ U₀) (h₂ : W₀ ≤ g ⁻¹ᵁ U₀) (x : Γ(X₀, U₀)) :
    (f.appLE U₀ W₀ h₁).hom x = (g.appLE U₀ W₀ h₂).hom x := by
  subst hfg
  rfl
private lemma snd_cancel_lemma {Z₀ : Scheme.{0}} (x y : (thickObj R I e G).left ⟶ Z₀)
    (h : (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ x =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ y) : x = y := by
  have h2 := congrArg ((lift (toUnit (thickObj R I e G) ≫ η[WeightPf.Te D.toPre I e])
    (𝟙 (thickObj R I e G))).left ≫ ·) h
  simpa only [← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp] using h2
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
theorem _root_.solution (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) jA)
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)
    (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) :
    ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom ((lhs U ιD e a χ u).s jA).val =
      ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) *
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hs).hom
        ((lhs U ιD e a χ u).s jA).val := by
  simp only [lhs]
  rw [appLE_mulGen, appLE_mulGen, ← _root_.mul_assoc]
  congr 1
  · have hact : ∀ k : Fin 4, (WeightPf.act (U.gt e)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k =
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
          D.toPre.Oφ (U.gt e).pG (star a • χ) k :=
      fun k => hA_act (U := U) (ιD := ιD) (e := e) (a := a) (χ := χ) (Sum.inl k)
    have key : ∀ k₁ k₂ : Fin 4,
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
            D.toPre.Oφ (U.gt e).pG (star a • χ) k₁ =
          (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
            D.toPre.Oφ (U.gt e).pG (star a • χ) k₂ →
        jA (Sum.inl k₁) = jA (Sum.inl k₂) :=
      fun k₁ k₂ h => cA (Sum.inl k₁) (Sum.inl k₂) (snd_cancel_lemma (e := e) _ _ h)
    have E := (U.gt e).t_weight (star a • χ) (jA ∘ Sum.inl)
      (Sum.elim (fun x => x.elim) (jA ∘ Sum.inl))
      (fun k₁ k₂ h => key k₁ k₂ ((hact k₁).symm.trans (h.trans (hact k₂))))
      (by
        rintro (k₁ | k₁) (k₂ | k₂) h <;>
          first | exact k₁.elim | exact k₂.elim | exact key k₁ k₂ h)
      (by
        rintro k (k' | k') h <;>
          first | exact k'.elim | exact key k k' ((hact k).symm.trans h))
    have h1 : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (star a • χ)) (jA ∘ Sum.inl) :=
      fun _ hz => wchart_inl_le D.toPre.P.L _ _ jA (ha hz)
    have h2 : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (star a • χ)) (jA ∘ Sum.inl) :=
      fun _ hz => wchart_inl_le D.toPre.P.L _ _ jA (hs hz)
    have hWa : W' ≤ LB.wchart D.toPre.P.L
        (fun k => (WeightPf.act (U.gt e)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k)
        (jA ∘ Sum.inl) :=
      fun _ hz => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h1 hz) k
    have hWb : W' ≤ LB.wchart D.toPre.P.L
        (Sum.elim (PEmpty.elim : PEmpty → _) (fun k => (snd (WeightPf.Te D.toPre I e)
          (thickObj R I e G)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k))
        (Sum.elim (fun x => x.elim) (jA ∘ Sum.inl)) := by
      intro z hz
      refine Set.mem_iInter.2 ?_
      rintro (k | k)
      · exact k.elim
      · exact Set.mem_iInter.1 (h2 hz) k
    have E' := corr_val_lemma _ _ _ _ E hWa hWb (le_inf hWa hWb)
    exact (pullGen_val_lemma ..).symm.trans (E'.trans ((mulGen_val_lemma ..).trans
      (congrArg₂ (· * ·) (charGen_val_lemma ..) (pullGen_val_lemma ..))))
  · exact (appLE_pullGen ..).trans ((appLE_congr_lemma (act_lift_xc (U := U) (e := e) (χ := χ)) ..).trans
      (appLE_pullGen ..).symm)
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
