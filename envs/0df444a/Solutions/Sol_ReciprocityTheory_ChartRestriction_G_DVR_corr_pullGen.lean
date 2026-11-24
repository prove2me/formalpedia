-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.corr_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:44.334691+00:00
-- url     : https://prove2.me/submissions/2c2095c0-f8fd-4c7d-acc7-a0e61c999b87

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
private lemma pullU_res_eq_res_pullU' {A B : Scheme.{0}} (g : B ⟶ A) {U V : A.Opens} (h : V ≤ U)
    (a : Γ(A, U)ˣ) :
    pullU g V (res h a) = res (fun _ hy => h hy : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U) (pullU g U a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp]
  exact congrArg (fun φ => φ.hom (a : Γ(A, U))) (g.naturality (homOfLE h).op)
private lemma res_pullU_eq_of_res_eq {A B : Scheme.{0}} (g : B ⟶ A) {U V V0 : A.Opens} {a : Γ(A, U)ˣ}
    {b : Γ(A, V)ˣ} {p : V0 ≤ U} {q : V0 ≤ V} (h : res p a = res q b) :
    res (fun _ hy => p hy : g ⁻¹ᵁ V0 ≤ g ⁻¹ᵁ U) (pullU g U a) =
      res (fun _ hy => q hy : g ⁻¹ᵁ V0 ≤ g ⁻¹ᵁ V) (pullU g V b) := by
  have h' := congrArg (pullU g V0) h
  rwa [pullU_res_eq_res_pullU', pullU_res_eq_res_pullU'] at h'
private lemma wchart_comp_inf_le_preimage_wchart_inf (g : Z ⟶ Y) (j : K → L.ι) (j' : K' → L.ι) :
    LB.wchart L (fun k => g ≫ φ k) j ⊓ LB.wchart L (fun k => g ≫ φ' k) j' ≤
      g ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := fun _ hx =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 k⟩
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
theorem _root_.solution {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') (g : Z ⟶ Y) :
    LB.Gen.Corr L _ ε _ ε' (LB.pullGen L φ ε t g) (LB.pullGen L φ' ε' t' g) := by
  intro j j' hc hc' hk
  have e0 := h j j' (fun k₁ k₂ e => hc k₁ k₂ (congrArg (g ≫ ·) e))
    (fun k₁ k₂ e => hc' k₁ k₂ (congrArg (g ≫ ·) e)) fun k k' e => hk k k' (congrArg (g ≫ ·) e)
  exact (res_res_lemma _ _ _).trans ((res_eq_res_of_le_of_res_eq (res_pullU_eq_of_res_eq g e0) (wchart_comp_inf_le_preimage_wchart_inf g j j') _ _).trans
    (res_res_lemma _ _ _).symm)
end ReciprocityTheory.ChartRestriction.G.DVR
