-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:13.774376+00:00
-- url     : https://prove2.me/submissions/5fa5ef17-c17a-471b-bd87-76fdf76218f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}
private lemma res_res_lemma {A : Scheme.{0}} {U V W : A.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (a : Γ(A, U)ˣ) : res h2 (res h1 a) = res (h2.trans h1) a := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  try rfl
private lemma pullU_res_eq_res_pullU' {A B : Scheme.{0}} (g : B ⟶ A) {U V : A.Opens} (h : V ≤ U)
    (a : Γ(A, U)ˣ) :
    pullU g V (res h a) = res (fun _ hy => h hy : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U) (pullU g U a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp]
  exact congrArg (fun φ => φ.hom (a : Γ(A, U))) (g.naturality (homOfLE h).op)
private lemma pullU_comp_lemma {A B C : Scheme.{0}} (g : B ⟶ A) (g' : C ⟶ B) {U : A.Opens}
    {O : C.Opens} (p : O ≤ g' ⁻¹ᵁ (g ⁻¹ᵁ U)) (q : O ≤ (g' ≫ g) ⁻¹ᵁ U) (x : Γ(A, U)ˣ) :
    res p (pullU g' _ (pullU g U x)) = res q (pullU (g' ≫ g) U x) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {W : Scheme.{0}} (g : Z ⟶ Y) (g' : W ⟶ Z) {U : Y.Opens} {U₁ : Z.Opens} {V₁ V₂ O : W.Opens}
    (h₁ : U₁ ≤ g ⁻¹ᵁ U) (k₁ : V₁ ≤ g' ⁻¹ᵁ U₁) (k₂ : V₂ ≤ (g' ≫ g) ⁻¹ᵁ U) (o₁ : O ≤ V₁) (o₂ : O ≤ V₂)
    (x : Γ(Y, U)ˣ) :
    res o₁ (res k₁ (pullU g' U₁ (res h₁ (pullU g U x)))) = res o₂ (res k₂ (pullU (g' ≫ g) U x)) := by
  simp only [pullU_res_eq_res_pullU', res_res_lemma]
  first
    | exact (res_res_lemma _ _ _).trans (pullU_comp_lemma _ _ _ _ _)
    | exact (res_res_lemma _ _ _).trans ((res_res_lemma _ _ _).trans (pullU_comp_lemma _ _ _ _ _))
end ReciprocityTheory.ChartRestriction.G.DVR
