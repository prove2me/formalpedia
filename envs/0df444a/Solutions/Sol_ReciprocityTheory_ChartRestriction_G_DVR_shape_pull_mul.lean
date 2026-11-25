-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:29.815099+00:00
-- url     : https://prove2.me/submissions/98d4863c-938b-4cb7-97b3-8d7671b74dc4

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
theorem _root_.solution (g : Z ⟶ Y) {U₁ U₂ W : Y.Opens} {Wz W₁ W₂ O Ow : Z.Opens}
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) (hz : Wz ≤ g ⁻¹ᵁ W) (hO : O ≤ Wz) (k₁ : W₁ ≤ g ⁻¹ᵁ U₁) (k₂ : W₂ ≤ g ⁻¹ᵁ U₂)
    (m₁ : Ow ≤ W₁) (m₂ : Ow ≤ W₂) (o : O ≤ Ow) (a : Γ(Y, U₁)ˣ) (b : Γ(Y, U₂)ˣ) :
    res hO (res hz (pullU g W (res h₁ a * res h₂ b))) =
      res o (res m₁ (res k₁ (pullU g U₁ a)) * res m₂ (res k₂ (pullU g U₂ b))) := by
  simp only [map_mul, pullU_res_eq_res_pullU', res_res_lemma]
  congr 1 <;> exact res_res_lemma _ _ _
end ReciprocityTheory.ChartRestriction.G.DVR
