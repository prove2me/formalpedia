-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.shape_mul_inv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:03.003789+00:00
-- url     : https://prove2.me/submissions/5988e7b8-d9d9-4104-b940-f86b4c93db5e

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
private lemma res_eq_res_of_le_of_res_eq {A : Scheme.{0}} {U V V0 O : A.Opens} {a : Γ(A, U)ˣ} {b : Γ(A, V)ˣ}
    {p : V0 ≤ U} {q : V0 ≤ V} (h : res p a = res q b) (hO : O ≤ V0) (r : O ≤ U) (s : O ≤ V) :
    res r a = res s b := by
  have h' := congrArg (res hO) h
  rwa [res_res_lemma, res_res_lemma] at h'
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
theorem _root_.solution {U U' O : Y.Opens} {W : Y.Opens} (h₁ : W ≤ U) (h₂ : W ≤ U') (o : O ≤ W) (x : Γ(Y, U)ˣ)
    (y : Γ(Y, U')ˣ) (hxy : res (inf_le_left : U ⊓ U' ≤ U) x = res (inf_le_right : U ⊓ U' ≤ U') y) :
    res o (res h₁ x * res h₂ y⁻¹) = 1 := by
  simp only [map_mul, map_inv, res_res_lemma]
  rw [res_eq_res_of_le_of_res_eq hxy (le_inf (o.trans h₁) (o.trans h₂)) _ (o.trans h₂), mul_inv_cancel]
end ReciprocityTheory.ChartRestriction.G.DVR
