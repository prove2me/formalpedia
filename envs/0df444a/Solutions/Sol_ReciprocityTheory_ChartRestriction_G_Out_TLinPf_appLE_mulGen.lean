-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.appLE_mulGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:29.369359+00:00
-- url     : https://prove2.me/submissions/4cf5496e-b983-49b0-b240-196840dea05c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
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
private lemma appLE_res_lemma {T₀ Z₀ : Scheme.{0}} (f : T₀ ⟶ Z₀) {V₀ U₀ : Z₀.Opens} (hVU : V₀ ≤ U₀)
    (W₀ : T₀.Opens) (h : W₀ ≤ f ⁻¹ᵁ V₀) (h' : W₀ ≤ f ⁻¹ᵁ U₀) (x : Γ(Z₀, U₀)ˣ) :
    (f.appLE V₀ W₀ h).hom (res hVU x).val = (f.appLE U₀ W₀ h').hom x.val := by
  rw [← Scheme.Hom.map_appLE f h (homOfLE hVU).op]
  rfl
end SlopeTestRemainingChoices
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
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
variable {Y Z : Scheme.{0}} (L : LB Y) {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution {T : Scheme.{0}} (f : T ⟶ Z) (φ : K → (Z ⟶ Y)) (ε : K → ℤ) (φ' : K' → (Z ⟶ Y))
    (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (j : K ⊕ K' → L.ι) (W' : T.Opens) (h : W' ≤ f ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j) :
    (f.appLE _ W' h).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      (f.appLE (LB.wchart L φ (j ∘ Sum.inl)) W' (fun _ hz => wchart_inl_le L φ φ' j (h hz))).hom (t.s (j ∘ Sum.inl)).val *
      (f.appLE (LB.wchart L φ' (j ∘ Sum.inr)) W' (fun _ hz => wchart_inr_le L φ φ' j (h hz))).hom (t'.s (j ∘ Sum.inr)).val := by
  simp only [LB.mulGen, Units.val_mul, map_mul]
  congr 1 <;> exact appLE_res_lemma _ _ _ _ _ _
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
