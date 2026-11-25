-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:18.144103+00:00
-- url     : https://prove2.me/submissions/474d1e48-c396-41d3-aa0b-2adc68ebad41

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
private lemma res_pullU_id' {A : Scheme.{0}} {U V : A.Opens} (h : V ≤ (𝟙 A) ⁻¹ᵁ U) (h' : V ≤ U)
    (x : Γ(A, U)ˣ) : res h (pullU (𝟙 A) U x) = res h' x := by
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
theorem _root_.solution {U : Y.Opens} {V O : Y.Opens} (h : V ≤ (𝟙 Y) ⁻¹ᵁ U) (o : O ≤ V) (o' : O ≤ U) (x : Γ(Y, U)ˣ) :
    res o (res h (pullU (𝟙 Y) U x)) = res o' x := by
  rw [res_res_lemma]
  exact res_pullU_id' _ _ x
end ReciprocityTheory.ChartRestriction.G.DVR
