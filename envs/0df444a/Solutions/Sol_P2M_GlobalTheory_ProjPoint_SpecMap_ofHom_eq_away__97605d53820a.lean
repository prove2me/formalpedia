-- Prove2me | solution 1 for P2M_GlobalTheory_ProjPoint_SpecMap_ofHom_eq_away__97605d53820a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:34.25511+00:00
-- url     : https://prove2.me/submissions/5c21fe91-d506-46a0-9c39-01c778cb9903

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Theorems.Thm_GlobalTheory_ProjPoint_ofHom_toSpecZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.ProjPoint.ofHom_toSpecZero

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.ProjPoint
theorem _root_.solution (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    (ψ : B →+* C) {f : A} {n : ℕ} (hn : 0 < n) (hf : f ∈ 𝒜 n) (hu : IsUnit (ψ (φ f))) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ofHom 𝒜 φ hφ =
      Spec.map (CommRingCat.ofHom (awayLift 𝒜 (ψ.comp φ) f hu)) ≫ Proj.awayι 𝒜 f hf hn := by
  set φ' := (Scheme.ΓSpecIso (.of B)).inv.hom.comp φ with hφ'
  have hφ'' := map_irrelevant_comp 𝒜 hφ (Scheme.ΓSpecIso (.of B)).inv.hom
  have hrange : Set.range (Spec.map (CommRingCat.ofHom ψ)) ⊆
      Set.range ((Spec (.of B)).basicOpen (φ' f)).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change _ ∈ (Spec (.of B)).basicOpen ((Scheme.ΓSpecIso (.of B)).inv (φ f))
    rw [basicOpen_eq_of_affine]
    exact fun h => x.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  let l := IsOpenImmersion.lift _ _ hrange
  have hl : l ≫ _ = _ := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : ((Spec (.of B)).basicOpen (φ' f)).ι ≫ ofHom 𝒜 φ hφ =
      Proj.toBasicOpenOfGlobalSections 𝒜 φ' rfl hn hf ≫ (Proj.basicOpen 𝒜 f).ι := by
    rw [← Proj.fromOfGlobalSections_resLE 𝒜 φ' hφ'' hn hf, Scheme.Hom.resLE_comp_ι]
    rfl
  rw [← hl, Category.assoc, h1, Proj.awayι, Proj.toBasicOpenOfGlobalSections]
  simp only [← Category.assoc]
  congr 2
  let ψ' : Γ(Spec (.of B), ⊤) →+* C := ψ.comp (Scheme.ΓSpecIso (.of B)).hom.hom
  have hψ' : ∀ a, ψ' (φ' a) = ψ (φ a) := by
    intro a
    simp [ψ', φ']
  have hu' : IsUnit (ψ' (φ' f)) := hψ' f ▸ hu
  have h2 : ((l ≫ ((Spec (.of B)).isoOfEq
      ((Spec (.of B)).toSpecΓ_preimage_basicOpen (φ' f))).inv) ≫
      (Spec (.of B)).toSpecΓ ∣_ (PrimeSpectrum.basicOpen (φ' f))) ≫
      (basicOpenIsoSpecAway (φ' f)).hom = Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.lift (S := Localization.Away (φ' f)) (φ' f) hu')) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Spec (.of B), ⊤) (Localization.Away (φ' f)))))]
    simp only [Category.assoc, basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_hom_fac,
      morphismRestrict_ι, Scheme.isoOfEq_inv_ι_assoc]
    rw [reassoc_of% hl, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp [ψ', IsLocalization.Away.lift_eq]
  rw [h2, ← Spec.map_comp]
  congr 2
  rw [← CommRingCat.ofHom_comp, awayLift, ← RingHom.comp_assoc]
  congr 2
  apply IsLocalization.ringHom_ext (M := .powers f)
  ext a
  simp [IsLocalization.Away.lift_eq, hψ']
end GlobalTheory.ProjPoint
