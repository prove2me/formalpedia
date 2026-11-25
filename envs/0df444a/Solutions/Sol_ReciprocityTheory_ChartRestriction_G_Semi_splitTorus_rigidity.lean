-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.splitTorus_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:36.161684+00:00
-- url     : https://prove2.me/submissions/0d0d3f44-0f7d-45fb-8fac-ea6ee56eea1d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_isUnit_single_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_appTop_comp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_over_appTop_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_comp_appTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_toUnit_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_chi_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus_const_mul_chi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus_const_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torus2_units

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open Rosenlicht
namespace ReciprocityTheory.ChartRestriction.G.Semi
theorem _root_.solution (K : Type u) [Field K] (X : Type u) [AddCommGroup X] [TwoUniqueSums X]
    (Y : Type u) [AddCommGroup Y]
    (f : splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X ⟶ splitTorus (Spec (.of K)) Y)
    (h1 : lift (𝟙 _) (toUnit _ ≫ η) ≫ f = toUnit _ ≫ η)
    (h2 : lift (toUnit _ ≫ η) (𝟙 _) ≫ f = toUnit _ ≫ η) :
    f = toUnit _ ≫ η := by
  apply coord_injective
  apply CommRingCat.hom_ext
  apply ringHom_ext_ZU
  intro y
  rw [coord_toUnit_comp]
  have capp : ∀ {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) (t : A),
      (φ ≫ ψ).hom t = ψ.hom (φ.hom t) := fun _ _ _ => rfl
  have idapp : ∀ (Z : Over (Spec (.of K))) (g : Z ⟶ Z) (t : Γ(Z.left, ⊤)), g = 𝟙 Z →
      g.left.appTop.hom t = t := by
    rintro Z g t rfl
    first
    | rfl
    | (simp; done)
  have etachi : ∀ x : X, (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom (chi X x) = (coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom (single x (1 : ULift.{u} ℤ)) := by
    intro x
    have h0 := congrArg (fun φ => φ.hom (single x (1 : ULift.{u} ℤ))) (coord_comp (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X) (𝟙 (splitTorus (Spec (.of K)) X)))
    simp only [Category.comp_id] at h0
    exact h0.symm
  have etaconst : ∀ t : Γ(Spec (.of K), ⊤), (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom ((splitTorus (Spec (.of K)) X).hom.appTop.hom t) = t := by
    intro t
    rw [← appTop_comp_apply, Over.w, ← toUnit_left]
    exact idapp _ _ t (toUnit_unique _ _)
  have s1f : ∀ z, (lift (𝟙 (splitTorus (Spec (.of K)) X)) (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X))).left.appTop.hom ((fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom z) = z := by
    intro z
    rw [over_appTop_comp, lift_fst]
    exact idapp _ _ z rfl
  have s1s : ∀ z, (lift (𝟙 (splitTorus (Spec (.of K)) X)) (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X))).left.appTop.hom ((snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom z) =
      (splitTorus (Spec (.of K)) X).hom.appTop.hom ((η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom z) := by
    intro z
    rw [over_appTop_comp, lift_snd, toUnit_comp_appTop]
  have s2f : ∀ z, (lift (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)) (𝟙 (splitTorus (Spec (.of K)) X))).left.appTop.hom ((fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom z) =
      (splitTorus (Spec (.of K)) X).hom.appTop.hom ((η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom z) := by
    intro z
    rw [over_appTop_comp, lift_fst, toUnit_comp_appTop]
  have s2s : ∀ z, (lift (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)) (𝟙 (splitTorus (Spec (.of K)) X))).left.appTop.hom ((snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom z) = z := by
    intro z
    rw [over_appTop_comp, lift_snd]
    exact idapp _ _ z rfl
  obtain ⟨c, a, b, hc, hw⟩ := torus2_units K X
    ((isUnit_single_one (R := ULift.{u} ℤ) y).map (coord f).hom)
  have k1 := congrArg (fun φ => (coord φ).hom (single y (1 : ULift.{u} ℤ))) h1
  have k2 := congrArg (fun φ => (coord φ).hom (single y (1 : ULift.{u} ℤ))) h2
  dsimp only at k1 k2
  rw [coord_toUnit_comp, coord_comp, capp, hw, map_mul (lift (𝟙 (splitTorus (Spec (.of K)) X)) (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X))).left.appTop.hom, s1f, s1s, etachi] at k1
  rw [coord_toUnit_comp, coord_comp, capp, hw, map_mul (lift (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)) (𝟙 (splitTorus (Spec (.of K)) X))).left.appTop.hom, s2f, s2s,
    map_mul (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom, etaconst, etachi] at k2
  have hea : IsUnit ((coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom (single a (1 : ULift.{u} ℤ)) : Γ(Spec (.of K), ⊤)) :=
    (isUnit_single_one (R := ULift.{u} ℤ) a).map (coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom
  have heb : IsUnit ((coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom (single b (1 : ULift.{u} ℤ)) : Γ(Spec (.of K), ⊤)) :=
    (isUnit_single_one (R := ULift.{u} ℤ) b).map (coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom
  have ha : a = 0 := torus_const_mul_chi K X (c₂ := (coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) Y)).hom (single y (1 : ULift.{u} ℤ)))
    (hc.mul heb) (by rw [map_mul, ← k1]; ring)
  have hb : b = 0 := torus_const_mul_chi K X (hc.mul hea) k2
  subst ha
  subst hb
  simp only [chi_zero, mul_one, map_one, ← AddMonoidAlgebra.one_def] at k1
  have hce := torus_const_injective K X k1
  rw [hw]
  simp only [chi_zero, mul_one, map_one]
  rw [hce, ← appTop_comp_apply, Over.w]
end ReciprocityTheory.ChartRestriction.G.Semi
