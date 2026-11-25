-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_pullbackSpec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:57:45.179446+00:00
-- url     : https://prove2.me/submissions/673a2cda-54d9-4062-be28-ef2a65e11c6a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__specMap_50eff1d20a13
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__zero__ef8e64a63a4e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolTo_of_affine

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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
private theorem valAt'_comp_lemma {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Y') (U : Y'.Opens)
    (f : Γ(Y', U)) : valAt' x (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_pos h', dif_pos h]
    unfold valAt
    first
      | (rw [Scheme.comp_appLE]) <;> rfl
      | (rw [Scheme.Hom.comp_appLE]) <;> rfl
      | simp [Scheme.comp_appLE]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_neg h', dif_neg h]
private theorem valAt'_top_mul_lemma_2 {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (f g : Γ(Y, ⊤)) :
    valAt' x ⊤ (f * g) = valAt' x ⊤ f * valAt' x ⊤ g := by
  have h : ⊤ ≤ x ⁻¹ᵁ (⊤ : Y.Opens) := by
    first
      | exact le_top
      | simp
  first
    | simp only [valAt', dif_pos h, valAt, map_mul]
    | simp [valAt', valAt, h]
private theorem valAt'_top_add_lemma_3 {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (f g : Γ(Y, ⊤)) :
    valAt' x ⊤ (f + g) = valAt' x ⊤ f + valAt' x ⊤ g := by
  have h : ⊤ ≤ x ⁻¹ᵁ (⊤ : Y.Opens) := by
    first
      | exact le_top
      | simp
  first
    | simp only [valAt', dif_pos h, valAt, map_add]
    | simp [valAt', valAt, h]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {B : Set V} (hB : IsOpen B)
    (w : V → (Sp ℂ ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T)))))
    (h1 : ∀ a : S, DifferentiableOn ℂ
      (fun b => valAt' (w b ≫ pullback.fst _ _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a)) B)
    (h2 : ∀ c : T, DifferentiableOn ℂ
      (fun b => valAt' (w b ≫ pullback.snd _ _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of T)).inv c)) B) :
    IsHolTo B w := by
  haveI : IsAffine (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T)))) := by
    first
      | infer_instance
      | exact isAffine_of_isIso (pullbackSpecIso R S T).hom
  refine isHolTo_of_affine hB ?_
  intro r

  have hL : ∀ (s : S) (b : V), valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv (s ⊗ₜ[R] (1 : T))) =
      valAt' (w b ≫ pullback.fst _ _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) := by
    intro s b
    first
      | rw [← pullbackSpecIso_hom_fst R S T]
      | rw [← Iso.hom_inv_id_assoc (pullbackSpecIso R S T) (pullback.fst _ _), pullbackSpecIso_inv_fst]
    (rw [← Category.assoc, valAt'_specMap]) <;> rfl
  have hR : ∀ (t : T) (b : V), valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv ((1 : S) ⊗ₜ[R] t)) =
      valAt' (w b ≫ pullback.snd _ _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of T)).inv t) := by
    intro t b
    first
      | rw [← pullbackSpecIso_hom_snd R S T]
      | rw [← Iso.hom_inv_id_assoc (pullbackSpecIso R S T) (pullback.snd _ _), pullbackSpecIso_inv_snd]
    (rw [← Category.assoc, valAt'_specMap]) <;> rfl
  have hS : ∀ s : S, DifferentiableOn ℂ (fun b => valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv (s ⊗ₜ[R] (1 : T)))) B :=
    fun s => (h1 s).congr (fun b _ => hL s b)
  have hT : ∀ t : T, DifferentiableOn ℂ (fun b => valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv ((1 : S) ⊗ₜ[R] t))) B :=
    fun t => (h2 t).congr (fun b _ => hR t b)

  have hAll : ∀ u : S ⊗[R] T, DifferentiableOn ℂ (fun b => valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv u)) B := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero, valAt'_zero']
      exact differentiableOn_const 0
    | tmul s t =>
      have hst : (s ⊗ₜ[R] t : S ⊗[R] T) = (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      simp only [hst, map_mul, valAt'_top_mul_lemma_2]
      exact (hS s).mul (hT t)
    | add x y hx hy =>
      simp only [map_add, valAt'_top_add_lemma_3]
      exact hx.add hy

  have hr : ∀ b, valAt' (w b) ⊤ r = valAt' (w b ≫ (pullbackSpecIso R S T).hom) ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).hom ((pullbackSpecIso R S T).inv.app ⊤ r))) := by
    intro b
    have hinv : (Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (S ⊗[R] T))).hom ((pullbackSpecIso R S T).inv.app ⊤ r)) =
        (pullbackSpecIso R S T).inv.app ⊤ r := by
      first
        | exact Iso.hom_inv_id_apply _ _
        | simp
    rw [hinv]
    have hw : w b = (w b ≫ (pullbackSpecIso R S T).hom) ≫ (pullbackSpecIso R S T).inv := by simp
    conv_lhs => rw [hw]
    exact (valAt'_comp_lemma (w b ≫ (pullbackSpecIso R S T).hom) (pullbackSpecIso R S T).inv ⊤ r).symm
  exact (hAll _).congr (fun b _ => hr b)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
