-- Prove2me | solution 1 for V3Glue.ChartInput.exists_iso_geometricFibre_strictTransform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a7b02e16-8f2b-5268-afd7-da0261761778

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry TopologicalSpace"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective basicOpen_eq_bot_iff Scheme.Hom Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

namespace RingHom.Flat

private theorem _root_.AlgebraicGeometry.RingHom.Flat.map_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B}
    (hφ : φ.Flat) {r : A} (hr : r ∈ nonZeroDivisors A) : φ r ∈ nonZeroDivisors B := by
  letI := φ.toAlgebra
  haveI : Module.Flat A B := hφ
  have hsm : IsSMulRegular B r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x : B, φ r * x = 0 → x = 0 := fun x hx =>
    hsm ((Algebra.smul_def r x).trans (hx.trans (smul_zero r).symm))
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx => key x ((mul_comm _ _).trans hx)⟩

end RingHom.Flat
p2m_export "AlgebraicGeometry" "RingHom.Flat.map_mem_nonZeroDivisors"
section

variable {T S Z : Scheme.{u}} (π : T ⟶ S) [Flat π] [IsIntegral S]
  (V : S.Opens) (hV : (V : Set S).Nonempty)
  (j : Z ⟶ T) [IsOpenImmersion j] [IsReduced Z] (hj : π ⁻¹ᵁ V ≤ j.opensRange)

include hV hj in

theorem isReduced_presheaf_obj_of_flat_of_le_preimage
    (W : S.affineOpens) (Q : T.affineOpens) (hle : (Q : T.Opens) ≤ π ⁻¹ᵁ (W : S.Opens))
    (hQ : ((Q : T.Opens) : Set T).Nonempty) :
    _root_.IsReduced Γ(T, Q) := by

  obtain ⟨t, ht⟩ := hQ
  haveI : Nonempty (W : S.Opens) := ⟨⟨π.base t, hle ht⟩⟩
  haveI : IsDomain Γ(S, W) := inferInstance

  obtain ⟨w, hwW, hwV⟩ : ((W : S.Opens) ⊓ V : S.Opens).1.Nonempty :=
    nonempty_preirreducible_inter (W : S.Opens).2 V.2 ⟨π.base t, hle ht⟩ hV
  obtain ⟨r, hrV, hwr⟩ := W.2.exists_basicOpen_le ⟨w, hwV⟩ hwW
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hwr
    exact hwr
  have hr : r ∈ nonZeroDivisors Γ(S, W) := mem_nonZeroDivisors_of_ne_zero hr0

  let φ := π.appLE W Q hle
  have hφ : φ.hom.Flat := HasRingHomProperty.appLE (P := @Flat) (f := π) inferInstance W Q hle
  set s : Γ(T, Q) := φ.hom r with hs
  have hsreg : s ∈ nonZeroDivisors Γ(T, Q) := hφ.map_mem_nonZeroDivisors hr

  haveI := Q.2.isLocalization_basicOpen s
  have hinj : Function.Injective (algebraMap Γ(T, Q) Γ(T, T.basicOpen s)) :=
    IsLocalization.injective (M := Submonoid.powers s) _ ((Submonoid.powers_le).mpr hsreg)

  have hbo : T.basicOpen s ≤ π ⁻¹ᵁ V := by
    have h1 : T.basicOpen s = (Q : T.Opens) ⊓ π ⁻¹ᵁ (S.basicOpen r) := by
      rw [hs]
      exact Scheme.basicOpen_appLE π (Q : T.Opens) (W : S.Opens) hle r
    rw [h1]
    exact inf_le_right.trans (fun x hx => hrV hx)
  have hbo' : T.basicOpen s ≤ j.opensRange := hbo.trans hj
  haveI : _root_.IsReduced Γ(T, T.basicOpen s) := by
    have e : Γ(T, T.basicOpen s) ≅ Γ(Z, j ⁻¹ᵁ (T.basicOpen s)) := by
      have h1 : j ''ᵁ (j ⁻¹ᵁ (T.basicOpen s)) = T.basicOpen s := by
        ext1
        change j.base '' (j.base ⁻¹' (T.basicOpen s : Set T)) = (T.basicOpen s : Set T)
        rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
        exact fun x hx => hbo' hx
      exact (T.presheaf.mapIso (eqToIso h1).op) ≪≫ (j.appIso (j ⁻¹ᵁ (T.basicOpen s)))
    exact isReduced_of_injective e.commRingCatIsoToRingEquiv e.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_injective _ hinj

include hV hj in

theorem isReduced_of_flat_of_isReduced_preimage : IsReduced T := by
  have key : ∀ t : T, ∃ (W : S.affineOpens) (Q : T.affineOpens),
      t ∈ (Q : T.Opens) ∧ (Q : T.Opens) ≤ π ⁻¹ᵁ (W : S.Opens) := by
    intro t
    obtain ⟨W, hWB, htW, -⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show π.base t ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨Q, hQB, htQ, hQle⟩ := (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens)
      (show t ∈ π ⁻¹ᵁ W from htW)
    exact ⟨⟨W, hWB⟩, ⟨Q, hQB⟩, htQ, hQle⟩
  choose W Q htQ hQle using key
  have hcov : ⨆ t : T, (Q t : T.Opens) = ⊤ := eq_top_iff.mpr fun t _ => Opens.mem_iSup.mpr ⟨t, htQ t⟩
  haveI : ∀ t : T, IsReduced ((T.openCoverOfIsOpenCover (fun t : T => ((Q t : T.Opens) : T.Opens)) hcov).X t) :=
    fun t => by
      change IsReduced ((Q t : T.Opens) : Scheme.{u})
      haveI : _root_.IsReduced Γ(T, Q t) :=
        isReduced_presheaf_obj_of_flat_of_le_preimage π V hV j hj (W t) (Q t) (hQle t) ⟨t, htQ t⟩
      haveI : _root_.IsReduced Γ((Q t : T.Opens), ⊤) :=
        isReduced_of_injective (Q t : T.Opens).topIso.commRingCatIsoToRingEquiv
          (Q t : T.Opens).topIso.commRingCatIsoToRingEquiv.injective
      exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ (T.openCoverOfIsOpenCover (fun t : T => ((Q t : T.Opens) : T.Opens)) hcov)

end

end AlgebraicGeometry

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective basicOpen_eq_bot_iff Scheme.Hom Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

section monoPullback

variable {C : Type*} [Category C] {S A B Z : C} (s : S ⟶ B) (a : A ⟶ B) (i : B ⟶ Z) [Mono i]
  [HasPullback s a] [HasPullback (s ≫ i) (a ≫ i)]

noncomputable def pullbackCompMonoIso : pullback (s ≫ i) (a ≫ i) ≅ pullback s a where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    ((cancel_mono i).mp (by simpa only [Category.assoc] using pullback.condition))
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_hom_fst : (pullbackCompMonoIso s a i).hom ≫ pullback.fst s a = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_hom_snd : (pullbackCompMonoIso s a i).hom ≫ pullback.snd s a = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_inv_fst : (pullbackCompMonoIso s a i).inv ≫ pullback.fst _ _ = pullback.fst s a :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_inv_snd : (pullbackCompMonoIso s a i).inv ≫ pullback.snd _ _ = pullback.snd s a :=
  pullback.lift_snd _ _ _

end monoPullback

theorem flat_pullback_fst_comp_mono {S A B Z : Scheme.{u}} (s : S ⟶ B) (a : A ⟶ B) (i : B ⟶ Z) [Mono i] [Flat a] :
    Flat (pullback.fst (s ≫ i) (a ≫ i)) := by
  rw [← pullbackCompMonoIso_hom_fst s a i]
  infer_instance

section factor

variable {S : Scheme.{u}} {O : Type u} [CommRing O] (f : S ⟶ Spec (CommRingCat.of O)) (I : Ideal O)

noncomputable def toΓ : O →+* Γ(S, ⊤) :=
  (f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom

theorem toΓ_apply (r : O) : toΓ f r = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv r) := rfl

theorem toΓ_eq_zero_of_preimage_basicOpen_eq_bot [IsReduced S] (r : O)
    (hr : f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥) : toΓ f r = 0 := by
  rw [← basicOpen_eq_bot_iff, toΓ_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hr

variable (hI : ∀ r ∈ I, f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥)

include hI in

theorem exists_lift_specQuotient [IsReduced S] :
    ∃ f' : S ⟶ Spec (CommRingCat.of (O ⧸ I)),
      f' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f := by
  have hker : ∀ r ∈ I, toΓ f r = 0 := fun r hr => toΓ_eq_zero_of_preimage_basicOpen_eq_bot f r (hI r hr)
  let φ : O ⧸ I →+* Γ(S, ⊤) := Ideal.Quotient.lift I (toΓ f) hker
  refine ⟨S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]

  rw [toΓ, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality f, Category.assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

end factor

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective basicOpen_eq_bot_iff Scheme.Hom Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

section basechange

variable {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (g' : S' ⟶ S) (g'' : S'' ⟶ S) (i : S'' ⟶ S') (hi : i ≫ g' = g'')

theorem isPullback_map_snd_snd :
    IsPullback (pullback.map f g'' f g' (𝟙 X) i (𝟙 S) (by simp) (by rw [Category.comp_id, hi]))
      (pullback.snd f g'') (pullback.snd f g') i := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f g') (v₁₃ := f) (h₂₂ := g') ?_ ?_ (IsPullback.of_hasPullback f g')
  · rw [pullback.lift_fst, Category.comp_id, hi]
    exact IsPullback.of_hasPullback f g''
  · rw [pullback.lift_snd]

end basechange
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

section strict

variable {S Y X Xκ B Bκ R : Scheme.{u}}

theorem exists_iso_pullback_of_isClosedImmersion_of_preimage_range_eq
    (ιS : S ⟶ Y) (toDR : Y ⟶ X) (πX : X ⟶ B) (toBase : Y ⟶ B) (hbase : toDR ≫ πX = toBase)
    (b : Bκ ⟶ B) (p₁ : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (hP : IsPullback p₁ p₂ πX b)
    (c : R ⟶ Xκ) [IsClosedImmersion c] [IsReduced R] [IsClosedImmersion (ιS ≫ toDR)]
    (hrange : p₁.base ⁻¹' Set.range (ιS ≫ toDR).base = Set.range c.base)
    [IsReduced (pullback (ιS ≫ toBase) b)] :
    ∃ e : pullback (ιS ≫ toBase) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧ e ≫ c ≫ p₁ = pullback.fst _ _ ≫ ιS ≫ toDR := by

  have hw : (pullback.fst (ιS ≫ toBase) b ≫ ιS ≫ toDR) ≫ πX = pullback.snd (ιS ≫ toBase) b ≫ b := by
    simp only [Category.assoc, hbase]
    exact pullback.condition
  let τ : pullback (ιS ≫ toBase) b ⟶ Xκ := hP.lift (pullback.fst _ _ ≫ ιS ≫ toDR) (pullback.snd _ _) hw
  have hτ₁ : τ ≫ p₁ = pullback.fst _ _ ≫ ιS ≫ toDR := hP.lift_fst _ _ _
  have hτ₂ : τ ≫ p₂ = pullback.snd _ _ := hP.lift_snd _ _ _

  let u : pullback (ιS ≫ toBase) b ⟶ pullback (ιS ≫ toDR) p₁ := pullback.lift (pullback.fst _ _) τ hτ₁.symm
  have hv : pullback.fst (ιS ≫ toDR) p₁ ≫ ιS ≫ toBase = (pullback.snd (ιS ≫ toDR) p₁ ≫ p₂) ≫ b := by
    rw [← hbase, Category.assoc, ← hP.w, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
      Category.assoc, Category.assoc]
  let v : pullback (ιS ≫ toDR) p₁ ⟶ pullback (ιS ≫ toBase) b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p₂) hv
  have hvτ : v ≫ τ = pullback.snd (ιS ≫ toDR) p₁ := by
    apply hP.hom_ext
    · rw [Category.assoc, hτ₁, ← Category.assoc, pullback.lift_fst, pullback.condition]
    · rw [Category.assoc, hτ₂, pullback.lift_snd]
  have huv : u ≫ v = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hτ₂, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, hvτ, Category.id_comp]
  haveI : IsIso u := ⟨⟨v, huv, hvu⟩⟩
  have hu : u ≫ pullback.snd (ιS ≫ toDR) p₁ = τ := pullback.lift_snd _ _ _

  haveI : IsClosedImmersion τ := by rw [← hu]; infer_instance
  have hsurj : Function.Surjective u.base := u.homeomorph.surjective
  have hτrange : Set.range τ.base = Set.range c.base := by
    rw [← hrange, ← hu, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_snd]
  obtain ⟨e, he⟩ := IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq τ c hτrange
  exact ⟨e.hom, inferInstance, by rw [← Category.assoc, he, hτ₂], by rw [← Category.assoc, he, hτ₁]⟩

end strict
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

section chart

variable {U Se Res F : Scheme.{u}} (f : U ⟶ Se) (ρ : Res ⟶ Se) (lam : F ⟶ Res)

theorem pullback_fst_snd_comp_fst_eq :
    pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ =
      (pullbackLeftPullbackSndIso f ρ lam).hom ≫ pullback.fst f (lam ≫ ρ) := by
  rw [pullbackLeftPullbackSndIso_hom_fst]

scoped instance isClosedImmersion_pullback_fst_snd_comp_fst [IsClosedImmersion (lam ≫ ρ)] :
    IsClosedImmersion (pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ) := by
  rw [pullback_fst_snd_comp_fst_eq]
  infer_instance

theorem range_pullback_fst_snd_comp_fst :
    Set.range (pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ).base =
      f.base ⁻¹' Set.range (lam ≫ ρ).base := by
  have hsurj : Function.Surjective (pullbackLeftPullbackSndIso f ρ lam).hom.base :=
    (pullbackLeftPullbackSndIso f ρ lam).hom.homeomorph.surjective
  rw [pullback_fst_snd_comp_fst_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

scoped instance etale_pullback_snd_snd [Etale f] : Etale (pullback.snd (pullback.snd f ρ) lam) := by
  have : pullback.snd (pullback.snd f ρ) lam = (pullbackLeftPullbackSndIso f ρ lam).hom ≫ pullback.snd f (lam ≫ ρ) := by
    rw [pullbackLeftPullbackSndIso_hom_snd]
  rw [this]
  infer_instance

end chart
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective basicOpen_eq_bot_iff Scheme.Hom Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

namespace V3Glue
p2m_export "V3Glue" "ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "ηG_inl compG coe_support_compG xU vertex Y q a j j_q toGlueInput hq g toB toB_eq πX Res X0 U mk S B ρ x thick x_mem_U f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section strict

variable {S : Scheme.{0}} (ιS : S ⟶ C.toGlueInput.glued)
  (im : Set X) (ξ : X) (hξ : IsGenericPoint ξ im) (hξ0 : ξ ∈ C.X0)
  (hS : Set.range ιS.base = closure {C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩})
  {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n)
  (horient : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base ↔ (y : X) ∈ im)
  (hxim : ∀ n, C.x n ∈ im)

include hξ hxim in
private theorem _root_.V3Glue.ChartInput.ξ_mem_U (n : N) : ξ ∈ C.U n :=
  (hξ.mem_open_set_iff (C.U n).2).mpr ⟨C.x n, hxim n, C.x_mem_U n⟩

p2m_export "V3Glue.ChartInput" "ξ_mem_U"

private def _root_.V3Glue.ChartInput.ηY (n : N) (hU : ξ ∈ C.U n) : C.Y n := (C.j n).base ⟨ξ, hU, hξ0⟩

p2m_export "V3Glue.ChartInput" "ηY"
private theorem _root_.V3Glue.ChartInput.ιY_ηY (n : N) (hU : ξ ∈ C.U n) :
    (C.toGlueInput.ιY n).base (C.ηY ξ hξ0 n hU) = C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩ := by
  have h := congr($(C.toGlueInput.homOfLE_ιX0 n).base ⟨ξ, hU, hξ0⟩)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [ηY]
  refine h.symm.trans ?_
  congr 1
  apply Subtype.ext
  simpa using congr($(X.homOfLE_ι (inf_le_right : C.U n ⊓ C.X0 ≤ C.X0)).base ⟨ξ, hU, hξ0⟩)

p2m_export "V3Glue.ChartInput" "ιY_ηY"
private theorem _root_.V3Glue.ChartInput.q_ηY (n : N) (hU : ξ ∈ C.U n) : (C.q n).base (C.ηY ξ hξ0 n hU) = ⟨ξ, hU⟩ := by
  have h := congr($(C.j_q n).base ⟨ξ, hU, hξ0⟩)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [ηY, h]
  apply Subtype.ext
  simpa using congr($(X.homOfLE_ι (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n)).base ⟨ξ, hU, hξ0⟩)

p2m_export "V3Glue.ChartInput" "q_ηY"

private theorem _root_.V3Glue.ChartInput.q_injOn_range_j (n : N) : Set.InjOn (C.q n).base (Set.range (C.j n).base) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  have ha := congr($(C.j_q n).base a)
  have hb := congr($(C.j_q n).base b)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at ha hb
  rw [ha, hb] at h
  rw [(X.homOfLE (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n)).isOpenEmbedding.injective h]

p2m_export "V3Glue.ChartInput" "q_injOn_range_j"

private scoped instance _root_.V3Glue.ChartInput.isClosedImmersion_G_q (n : N) [IsClosedImmersion (lam n ≫ C.ρ n)] :
    IsClosedImmersion (pullback.fst (C.g n) (lam n) ≫ C.q n) :=
  AlgebraicGeometry.isClosedImmersion_pullback_fst_snd_comp_fst (C.f n) (C.ρ n) (lam n)

p2m_export "V3Glue.ChartInput" "isClosedImmersion_G_q"
include horient in

private theorem _root_.V3Glue.ChartInput.range_G_q (n : N) :
    Set.range (pullback.fst (C.g n) (lam n) ≫ C.q n).base = {y : C.U n | (y : X) ∈ im} := by
  exact (AlgebraicGeometry.range_pullback_fst_snd_comp_fst (C.f n) (C.ρ n) (lam n)).trans
    (Set.ext fun y => horient n y)

p2m_export "V3Glue.ChartInput" "range_G_q"
include hξ horient hxim in

private theorem _root_.V3Glue.ChartInput.range_G (n : N) [IsClosedImmersion (lam n)] [IsClosedImmersion (lam n ≫ C.ρ n)] :
    Set.range (pullback.fst (C.g n) (lam n)).base = closure {C.ηY ξ hξ0 n (C.ξ_mem_U im ξ hξ hxim n)} := by
  have hU := C.ξ_mem_U im ξ hξ hxim n
  have hqη : (C.q n).base (C.ηY ξ hξ0 n hU) = ⟨ξ, hU⟩ := C.q_ηY ξ hξ0 n hU
  have hrange : Set.range (pullback.fst (C.g n) (lam n) ≫ C.q n).base = {y : C.U n | (y : X) ∈ im} :=
    C.range_G_q im lam horient n

  obtain ⟨z₀, hz₀⟩ : C.ηY ξ hξ0 n hU ∈ Set.range (pullback.fst (C.g n) (lam n)).base := by
    have h1 : (C.q n).base (C.ηY ξ hξ0 n hU) ∈ Set.range (pullback.fst (C.g n) (lam n) ≫ C.q n).base := by
      rw [hrange, hqη]; exact hξ.mem
    obtain ⟨z, hz⟩ := h1
    rw [Scheme.Hom.comp_base, TopCat.comp_app] at hz
    refine ⟨z, C.q_injOn_range_j n ?_ ⟨_, rfl⟩ hz⟩
    apply C.hq
    rw [hz, hqη]
    exact hξ0
  haveI : IsClosedImmersion (pullback.fst (C.g n) (lam n)) := MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance
  set h := pullback.fst (C.g n) (lam n) ≫ C.q n with hh
  have h3 : h.base z₀ = (C.q n).base (C.ηY ξ hξ0 n hU) := by
    rw [hh, Scheme.Hom.comp_base, TopCat.comp_app, hz₀]
  have hι3 : (C.U n).ι.base (h.base z₀) = ξ := by
    rw [h3, hqη]
    simp
  have hmem : ∀ w, (C.U n).ι.base (h.base w) ∈ im := fun w => by
    have hw : h.base w ∈ Set.range h.base := ⟨w, rfl⟩
    rw [hrange] at hw
    simp at hw
    exact hw
  have hindU : Topology.IsInducing (C.U n).ι.base := (C.U n).ι.isOpenEmbedding.isInducing
  have hindh : Topology.IsInducing h.base := h.isClosedEmbedding.isInducing
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have hz' : z ∈ closure {z₀} := by
      rw [hindh.closure_eq_preimage_closure_image, Set.image_singleton, Set.mem_preimage,
        hindU.closure_eq_preimage_closure_image, Set.image_singleton, hι3, hξ.def, Set.mem_preimage]
      exact hmem z
    have h4 := image_closure_subset_closure_image (pullback.fst (C.g n) (lam n)).continuous ⟨z, hz', rfl⟩
    rwa [Set.image_singleton, hz₀] at h4
  · exact closure_minimal (Set.singleton_subset_iff.mpr ⟨z₀, hz₀⟩)
      (pullback.fst (C.g n) (lam n)).isClosedEmbedding.isClosed_range

p2m_export "V3Glue.ChartInput" "range_G"
include hξ horient hxim in

private theorem _root_.V3Glue.ChartInput.preimage_ιY_closure_eq_preimage_g_range (n : N) [IsClosedImmersion (lam n)] [IsClosedImmersion (lam n ≫ C.ρ n)] :
    (C.toGlueInput.ιY n).base ⁻¹' closure {C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩} =
      (C.g n).base ⁻¹' Set.range (lam n).base := by
  rw [← Scheme.Pullback.range_fst, C.range_G im ξ hξ hξ0 lam horient hxim n,
    IsOpenMap.preimage_closure_eq_closure_preimage (C.toGlueInput.ιY n).isOpenEmbedding.isOpenMap
      (C.toGlueInput.ιY n).continuous]
  congr 1
  rw [← C.ιY_ηY ξ hξ0 n (C.ξ_mem_U im ξ hξ hxim n)]
  exact Set.ext fun y => (C.toGlueInput.ιY n).isOpenEmbedding.injective.eq_iff

p2m_export "V3Glue.ChartInput" "preimage_ιY_closure_eq_preimage_g_range"
end strict
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry"

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput"
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective basicOpen_eq_bot_iff Scheme.Hom Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

theorem isClosedImmersion_morphismRestrict_of_isPullback {P S X : Scheme.{0}} {U : X.Opens} {ψ : S ⟶ X}
    {f' : P ⟶ U} {i : P ⟶ S} (sq : IsPullback f' i U.ι ψ) (hf' : IsClosedImmersion f') :
    IsClosedImmersion (ψ ∣_ U) := by
  have h := IsPullback.isoIsPullback_hom_fst (h := isPullback_morphismRestrict ψ U) (h' := sq)
  rw [← h]
  infer_instance

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput"

namespace V3Glue
p2m_export "V3Glue" "ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "ηG_inl compG coe_support_compG xU vertex Y q a j j_q toGlueInput hq g toB toB_eq πX Res X0 U mk S B ρ x thick x_mem_U f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  {S : Scheme.{0}} (ιS : S ⟶ C.toGlueInput.glued)
  (im : Set X) (ξ : X) (hξ : IsGenericPoint ξ im) (hξ0 : ξ ∈ C.X0)
  (hS : Set.range ιS.base = closure {C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩})
  {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n)
  (horient : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base ↔ (y : X) ∈ im)
  (hxim : ∀ n, C.x n ∈ im)

include hξ hS horient hxim in

private theorem _root_.V3Glue.ChartInput.exists_iso_strictPiece (n : N) [IsClosedImmersion ιS] [IsReduced S] [IsClosedImmersion (lam n)]
    [IsClosedImmersion (lam n ≫ C.ρ n)] [IsReduced (pullback (C.g n) (lam n))] :
    ∃ e : pullback ιS (C.toGlueInput.ιY n) ≅ pullback (C.g n) (lam n),
      e.hom ≫ pullback.fst (C.g n) (lam n) = pullback.snd ιS (C.toGlueInput.ιY n) := by
  haveI : IsReduced (pullback ιS (C.toGlueInput.ιY n)) :=
    isReduced_of_isOpenImmersion (pullback.fst ιS (C.toGlueInput.ιY n))
  have hsnd : IsClosedImmersion (pullback.snd ιS (C.toGlueInput.ιY n)) :=
    MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance
  have hfst : IsClosedImmersion (pullback.fst (C.g n) (lam n)) :=
    MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance
  have hr : Set.range (pullback.snd ιS (C.toGlueInput.ιY n)).base =
      Set.range (pullback.fst (C.g n) (lam n)).base := by
    rw [Scheme.Pullback.range_snd, hS, Scheme.Pullback.range_fst]
    exact C.preimage_ιY_closure_eq_preimage_g_range im ξ hξ hξ0 lam horient hxim n
  exact @AlgebraicGeometry.IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq _ _ _
    (pullback.snd ιS (C.toGlueInput.ιY n)) (pullback.fst (C.g n) (lam n)) hsnd hfst inferInstance inferInstance hr

p2m_export "V3Glue.ChartInput" "exists_iso_strictPiece"
include hξ hS horient hxim in

private theorem _root_.V3Glue.ChartInput.isClosedImmersion_comp_toDR [IsClosedImmersion ιS] [IsReduced S] [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))] :
    IsClosedImmersion (ιS ≫ C.toGlueInput.toDR) := by
  let Uc : Option N → X.Opens := fun i => i.elim C.X0 C.U
  have hU : ⨆ i, Uc i = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    by_cases hx : ∀ n, x ≠ C.x n
    · exact Opens.mem_iSup.mpr ⟨none, (C.mem_X0 x).mpr hx⟩
    · push Not at hx
      obtain ⟨n, rfl⟩ := hx
      exact Opens.mem_iSup.mpr ⟨some n, C.x_mem_U n⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top Uc hU
  rintro (_ | n)
  ·
    change IsClosedImmersion ((ιS ≫ C.toGlueInput.toDR) ∣_ C.X0)
    have sq : IsPullback (pullback.snd ιS C.toGlueInput.ιX0 ≫ 𝟙 _) (pullback.fst ιS C.toGlueInput.ιX0)
        C.X0.ι (ιS ≫ C.toGlueInput.toDR) :=
      (IsPullback.of_hasPullback ιS C.toGlueInput.ιX0).flip.paste_horiz (C.toGlueInput.isPullback_ιX0 C.hq)
    rw [Category.comp_id] at sq
    have hsnd : IsClosedImmersion (pullback.snd ιS C.toGlueInput.ιX0) :=
      MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance
    exact AlgebraicGeometry.isClosedImmersion_morphismRestrict_of_isPullback sq hsnd
  ·
    change IsClosedImmersion ((ιS ≫ C.toGlueInput.toDR) ∣_ C.U n)
    have sq : IsPullback (pullback.snd ιS (C.toGlueInput.ιY n) ≫ C.q n) (pullback.fst ιS (C.toGlueInput.ιY n))
        (C.U n).ι (ιS ≫ C.toGlueInput.toDR) :=
      (IsPullback.of_hasPullback ιS (C.toGlueInput.ιY n)).flip.paste_horiz (C.toGlueInput.isPullback_ιY C.hq n)
    obtain ⟨e, he⟩ := C.exists_iso_strictPiece ιS im ξ hξ hξ0 hS lam horient hxim n
    have hE : pullback.snd ιS (C.toGlueInput.ιY n) ≫ C.q n =
        e.hom ≫ (pullback.fst (C.g n) (lam n) ≫ C.q n) := by
      rw [← he]; exact Category.assoc _ _ _
    have hcomp : IsClosedImmersion (pullback.snd ιS (C.toGlueInput.ιY n) ≫ C.q n) := by
      rw [hE]
      exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.hom _).mpr
        (C.isClosedImmersion_G_q lam n)
    exact AlgebraicGeometry.isClosedImmersion_morphismRestrict_of_isPullback sq hcomp

p2m_export "V3Glue.ChartInput" "isClosedImmersion_comp_toDR"
include hξ hS in

private theorem _root_.V3Glue.ChartInput.range_comp_toDR [IsClosedImmersion (ιS ≫ C.toGlueInput.toDR)] :
    Set.range (ιS ≫ C.toGlueInput.toDR).base = im := by
  have hx0 : C.toGlueInput.toDR.base (C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩) = ξ := by
    have h := congr($(C.toGlueInput.ιX0_toDR).base ⟨ξ, hξ0⟩)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [h]
    simp
  apply le_antisymm
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hS, ← hξ.def]
    refine (image_closure_subset_closure_image C.toGlueInput.toDR.continuous).trans ?_
    rw [Set.image_singleton, hx0]
  · rw [← hξ.def]
    refine closure_minimal ?_ (ιS ≫ C.toGlueInput.toDR).isClosedEmbedding.isClosed_range
    rw [Set.singleton_subset_iff]
    have hη : C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩ ∈ Set.range ιS.base := by
      rw [hS]; exact subset_closure rfl
    obtain ⟨s, hs⟩ := hη
    exact ⟨s, by rw [Scheme.Hom.comp_base, TopCat.comp_app, hs, hx0]⟩

p2m_export "V3Glue.ChartInput" "range_comp_toDR"
include hξ hS horient hxim in

private theorem _root_.V3Glue.ChartInput.isReduced_pullback_strict [IsClosedImmersion ιS] [IsIntegral S] [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))]
    (n₀ : N) {Bκ B₀ : Scheme.{0}} (i : B₀ ⟶ C.B) [Mono i] (a : Bκ ⟶ B₀) [Flat a] (s₀ : S ⟶ B₀)
    (hsB : ιS ≫ C.toGlueInput.toDR ≫ C.πX = s₀ ≫ i)
    (sB : S ⟶ C.B) (b : Bκ ⟶ C.B) (hs : sB = s₀ ≫ i) (hb : b = a ≫ i)
    (hGκ : IsReduced (pullback (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) b)) :
    IsReduced (pullback sB b) := by
  subst hs hb
  haveI : Flat (pullback.fst (s₀ ≫ i) (a ≫ i)) := AlgebraicGeometry.flat_pullback_fst_comp_mono s₀ a i

  have hU := C.ξ_mem_U im ξ hξ hxim n₀
  have hV : ((pullback.fst ιS (C.toGlueInput.ιY n₀)).opensRange : Set S).Nonempty := by
    have hη : C.toGlueInput.ιX0.base ⟨ξ, hξ0⟩ ∈ Set.range ιS.base := by
      rw [hS]; exact subset_closure rfl
    obtain ⟨s, hs⟩ := hη
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ιS) (g := C.toGlueInput.ιY n₀)
      s (C.ηY ξ hξ0 n₀ hU) (hs.trans (C.ιY_ηY ξ hξ0 n₀ hU).symm)
    exact ⟨(pullback.fst ιS (C.toGlueInput.ιY n₀)).base w, ⟨w, rfl⟩⟩

  obtain ⟨e, he⟩ := C.exists_iso_strictPiece ιS im ξ hξ hξ0 hS lam horient hxim n₀
  have h2' : C.q n₀ ≫ (C.U n₀).ι = C.toGlueInput.ιY n₀ ≫ C.toGlueInput.toDR := (C.toGlueInput.ιY_toDR n₀).symm
  have hcond : pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ ιS =
      pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toGlueInput.ιY n₀ := pullback.condition
  have E1 : pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ s₀ ≫ i =
      (pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ ιS) ≫ (C.toGlueInput.toDR ≫ C.πX) := by
    rw [← hsB]; exact (Category.assoc _ _ _).symm
  have E2 : (pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ ιS) ≫ (C.toGlueInput.toDR ≫ C.πX) =
      (pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toGlueInput.ιY n₀) ≫ (C.toGlueInput.toDR ≫ C.πX) := by
    rw [hcond]
  have E3 : (pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toGlueInput.ιY n₀) ≫ (C.toGlueInput.toDR ≫ C.πX) =
      pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ ((C.toGlueInput.ιY n₀ ≫ C.toGlueInput.toDR) ≫ C.πX) := by
    simp only [Category.assoc]
  have E4 : pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ ((C.toGlueInput.ιY n₀ ≫ C.toGlueInput.toDR) ≫ C.πX) =
      pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ ((C.q n₀ ≫ (C.U n₀).ι) ≫ C.πX) :=
    congrArg (fun k => pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ k ≫ C.πX) h2'.symm
  have E5 : pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ ((C.q n₀ ≫ (C.U n₀).ι) ≫ C.πX) =
      pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toB n₀ := by
    rw [C.toB_eq]; congr 1
  have E6 : pullback.snd ιS (C.toGlueInput.ιY n₀) ≫ C.toB n₀ =
      (e.hom ≫ pullback.fst (C.g n₀) (lam n₀)) ≫ C.toB n₀ :=
    congrArg (· ≫ C.toB n₀) he.symm
  have hcomm : pullback.fst ιS (C.toGlueInput.ιY n₀) ≫ s₀ ≫ i =
      (e.hom ≫ pullback.fst (C.g n₀) (lam n₀)) ≫ C.toB n₀ :=
    E1.trans (E2.trans (E3.trans (E4.trans (E5.trans E6))))
  haveI : IsReduced (pullback e.hom (pullback.fst (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) (a ≫ i))) :=
    isReduced_of_isOpenImmersion
      (pullback.snd e.hom (pullback.fst (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) (a ≫ i)))
  haveI : IsReduced (pullback (e.hom ≫ pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) (a ≫ i)) :=
    isReduced_of_isOpenImmersion
      (pullbackRightPullbackFstIso (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) (a ≫ i) e.hom).inv
  haveI : IsReduced (pullback (pullback.fst ιS (C.toGlueInput.ιY n₀)) (pullback.fst (s₀ ≫ i) (a ≫ i))) :=
    isReduced_of_isOpenImmersion
      ((pullbackRightPullbackFstIso (s₀ ≫ i) (a ≫ i) (pullback.fst ιS (C.toGlueInput.ιY n₀))).hom ≫
        (pullback.congrHom hcomm rfl).hom ≫ (pullback.congrHom (Category.assoc _ _ _) rfl).hom)
  exact AlgebraicGeometry.isReduced_of_flat_of_isReduced_preimage (pullback.fst (s₀ ≫ i) (a ≫ i))
    (pullback.fst ιS (C.toGlueInput.ιY n₀)).opensRange hV
    (pullback.snd (pullback.fst ιS (C.toGlueInput.ιY n₀)) (pullback.fst (s₀ ≫ i) (a ≫ i)))
    (fun x hx => by
      show x ∈ Set.range (pullback.snd (pullback.fst ιS (C.toGlueInput.ιY n₀)) (pullback.fst (s₀ ≫ i) (a ≫ i))).base
      rw [Scheme.Pullback.range_snd]
      exact hx)

p2m_export "V3Glue.ChartInput" "isReduced_pullback_strict"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput"
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput"

end
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput"

p2m_open "AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry CategoryTheory TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective basicOpen_eq_bot_iff Scheme.Hom Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen Hom mk Γ empty Pullback.range_fst topIso IdealSheafData.range_subschemeι toSpecΓ_naturality basicOpen_zero Hom.comp_base Pullback.range_snd affineOpens basicOpen basicOpen_appLE preimage_basicOpen_top openCoverOfIsOpenCover isBasis_affineOpens Opens homOfLE_ι Pullback.exists_preimage_pullback IdealSheafData ΓSpecIso toSpecΓ"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "radical coe_support_vanishingIdeal mk map subscheme range_subschemeι map_id vanishingIdeal vanishingIdeal_ideal ideal map_comp subschemeι comap subschemeCover support"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem isReduced_Spec_of_isReduced (R : Type u) [CommRing R] [_root_.IsReduced R] :
    IsReduced (Spec (CommRingCat.of R)) := by
  haveI : _root_.IsReduced Γ(Spec (CommRingCat.of R), ⊤) :=
    isReduced_of_injective (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isAffine_isReduced _

theorem isReduced_subscheme_of_isRadical (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) : IsReduced I.subscheme := by
  haveI : ∀ i, IsReduced (I.subschemeCover.openCover.X i) := fun (U : X.affineOpens) => by
    change IsReduced (Spec (CommRingCat.of (Γ(X, (U : X.Opens)) ⧸ I.ideal U)))
    haveI : _root_.IsReduced (Γ(X, (U : X.Opens)) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (hI U)
    exact isReduced_Spec_of_isReduced _
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

scoped instance isReduced_subscheme_vanishingIdeal (Z : Closeds X) : IsReduced (vanishingIdeal Z).subscheme :=
  isReduced_subscheme_of_isRadical _ fun U => by
    rw [vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _

theorem isIntegral_subscheme_vanishingIdeal_closure_singleton (x : X) :
    IsIntegral (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme := by
  set I : X.IdealSheafData := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
  have hsupp : (I.support : Set X) = closure {x} := by
    rw [coe_support_vanishingIdeal]; rfl

  have hx : x ∈ Set.range I.subschemeι.base := by
    rw [range_subschemeι, hsupp]; exact subset_closure rfl
  obtain ⟨s, hs⟩ := hx

  have hind : Topology.IsInducing I.subschemeι.base := I.subschemeι.isClosedEmbedding.isInducing
  have hgen : closure ({s} : Set I.subscheme) = Set.univ := by
    rw [hind.closure_eq_preimage_closure_image, Set.image_singleton, hs, ← hsupp, ← range_subschemeι,
      Set.preimage_range]
  haveI : IrreducibleSpace I.subscheme := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hgen]
    exact isIrreducible_singleton.closure
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective basicOpen_eq_bot_iff Scheme.Hom Scheme.Pullback.range_fst isPullback_morphismRestrict IsZariskiLocalAtTarget Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat IsClosedImmersion IsReduced HasRingHomProperty.appLE SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id IsZariskiLocalAtTarget.of_iSup_eq_top Etale isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq"
p2m_open "AlgebraicGeometry"

theorem isGenericPoint_image_genericPoint {R X : Scheme.{u}} [IsIntegral R] (h : R ⟶ X) :
    IsGenericPoint (h.base (genericPoint R)) (closure (Set.range h.base)) := by
  have := (genericPoint_spec R).image h.continuous
  rwa [Set.image_univ] at this

theorem range_specMap_of_ker_eq_maximalIdeal {O κ : Type u} [CommRing O] [IsLocalRing O] [Field κ]
    (φ : O →+* κ) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal O) :
    Set.range (Spec.map (CommRingCat.ofHom φ)).base = {IsLocalRing.closedPoint O} := by
  have key : ∀ y : PrimeSpectrum κ, (Spec.map (CommRingCat.ofHom φ)).base y = IsLocalRing.closedPoint O := by
    intro y
    apply PrimeSpectrum.ext
    have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    change Ideal.comap φ y.asIdeal = IsLocalRing.maximalIdeal O
    rw [hy, ← RingHom.ker_eq_comap_bot, hker]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, key _⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact key y

theorem IsPullback.range_fst' {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  have hsurj : Function.Surjective h.isoPullback.hom.base := h.isoPullback.hom.homeomorph.surjective
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

theorem iff_mem_closure_of_orientation {R Xκ X : Scheme.{u}} (c : R ⟶ Xκ) (bcm : Xκ ⟶ X) {U : X.Opens}
    (P : U → Prop)
    (hfwd : ∀ y : U, P y → (y : X) ∈ Set.range (c ≫ bcm).base)
    (hconv : ∀ y : U, (y : X) ∈ Set.range (c ≫ bcm).base → P y)
    (hdesc : bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) = Set.range c.base)
    (hfib : closure (Set.range (c ≫ bcm).base) ⊆ Set.range bcm.base) (y : U) :
    P y ↔ (y : X) ∈ closure (Set.range (c ≫ bcm).base) := by
  have him : Set.range (c ≫ bcm).base = bcm.base '' Set.range c.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  constructor
  · exact fun h => subset_closure (hfwd y h)
  · intro h
    apply hconv
    obtain ⟨r, hr⟩ := hfib h
    rw [him] at h ⊢
    have hr' : r ∈ bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) := by
      rw [Set.mem_preimage, hr]; exact h
    rw [hdesc] at hr'
    exact ⟨r, hr', hr⟩

theorem closure_subset_preimage_singleton {X B : Scheme.{u}} (π : X ⟶ B) {s : Set X} {b : B}
    (hb : IsClosed ({b} : Set B)) (hs : s ⊆ π.base ⁻¹' {b}) : closure s ⊆ π.base ⁻¹' {b} :=
  closure_minimal hs (hb.preimage π.continuous)

theorem preimage_basicOpen_eq_bot_of_forall_eq_closedPoint {S : Scheme.{u}} {O : Type u} [CommRing O] [IsLocalRing O]
    (f : S ⟶ Spec (CommRingCat.of O)) (hf : ∀ s : S, f.base s = IsLocalRing.closedPoint O) (r : O)
    (hr : r ∈ IsLocalRing.maximalIdeal O) :
    f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥ := by
  ext s
  simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hs
  have hs' : f.base s ∈ PrimeSpectrum.basicOpen r := hs
  rw [hf s] at hs'
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hs' hr

theorem forall_comp_eq_of_range_eq_closure {S Y B : Scheme.{u}} (ιS : S ⟶ Y) (g : Y ⟶ B) {y : Y} {b : B}
    (hS : Set.range ιS.base = closure {y}) (hy : g.base y = b) (hb : IsClosed ({b} : Set B)) (s : S) :
    (ιS ≫ g).base s = b := by
  have h1 : closure {y} ⊆ g.base ⁻¹' {b} :=
    closure_subset_preimage_singleton g hb (by rintro _ rfl; exact hy)
  have h2 : ιS.base s ∈ closure {y} := by rw [← hS]; exact ⟨s, rfl⟩
  exact h1 h2

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace V3Glue
p2m_export "V3Glue" "ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "ηG_inl compG coe_support_compG xU vertex Y q a j j_q toGlueInput hq g toB toB_eq πX Res X0 U mk S B ρ x thick x_mem_U f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry TopologicalSpace"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private theorem _root_.V3Glue.ChartInput.strict_iso_of
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (j : Fin 2)

    {R Xκ Bκ : Scheme.{0}} (c : R ⟶ Xκ) [IsClosedImmersion c] [IsIntegral R]
    (bcm : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (b : Bκ ⟶ C.B) (hP : IsPullback bcm p₂ C.πX b)
    (hξj : ξ j = (c ≫ bcm).base (genericPoint R))
    (hdesc : bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) = Set.range c.base)
    {pt : C.B} (hpt : IsClosed ({pt} : Set C.B)) (hfib : Set.range bcm.base = C.πX.base ⁻¹' {pt})
    (hcpt : ∀ r : R, (c ≫ bcm ≫ C.πX).base r = pt)

    {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n) [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))]
    (horient_fwd : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base →
      (y : X) ∈ Set.range (c ≫ bcm).base)
    (horient_conv : ∀ n (y : C.U n), (y : X) ∈ Set.range (c ≫ bcm).base →
      (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base)
    (hxim : ∀ n, C.x n ∈ Set.range (c ≫ bcm).base)

    (n₀ : N) {B₀ : Scheme.{0}} (i : B₀ ⟶ C.B) [Mono i] (a : Bκ ⟶ B₀) [Flat a] (hb : b = a ≫ i)
    (s₀ : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subscheme ⟶ B₀)
    (hsB : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX = s₀ ≫ i)
    (hGκ : IsReduced (pullback (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) b)) :
    ∃ e : pullback ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧
        e ≫ c ≫ bcm = pullback.fst _ _ ≫ (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR := by

  set im : Set X := closure (Set.range (c ≫ bcm).base) with him
  have hgen : IsGenericPoint (ξ j) im := by
    rw [hξj]; exact AlgebraicGeometry.isGenericPoint_image_genericPoint (c ≫ bcm)
  have hS : Set.range (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι.base = closure {C.toGlueInput.ιX0.base ⟨ξ j, hξ j⟩} := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_compG, ηG_inl]
  have horient : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base ↔ (y : X) ∈ im := by
    intro n y
    refine AlgebraicGeometry.iff_mem_closure_of_orientation c bcm
      (fun y : C.U n => (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base) (horient_fwd n) (horient_conv n) hdesc ?_ y
    rw [hfib]
    refine AlgebraicGeometry.closure_subset_preimage_singleton C.πX hpt ?_
    rintro _ ⟨r, rfl⟩
    exact hcpt r
  have hxim' : ∀ n, C.x n ∈ im := fun n => subset_closure (hxim n)

  haveI : IsIntegral (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure_singleton _

  haveI hG1 : IsClosedImmersion ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR) :=
    C.isClosedImmersion_comp_toDR (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι im (ξ j) hgen (hξ j) hS lam horient hxim'

  have hG2 : bcm.base ⁻¹' Set.range ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR).base = Set.range c.base := by
    rw [C.range_comp_toDR (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι im (ξ j) hgen (hξ j) hS, him, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp]
    exact hdesc

  haveI hG3 : IsReduced (pullback ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX) b) :=
    C.isReduced_pullback_strict (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι im (ξ j) hgen (hξ j) hS lam horient hxim' n₀ i a s₀ hsB _ b hsB hb hGκ

  exact AlgebraicGeometry.exists_iso_pullback_of_isClosedImmersion_of_preimage_range_eq (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι
    C.toGlueInput.toDR C.πX (C.toGlueInput.toDR ≫ C.πX) rfl b bcm p₂ hP c hG2

p2m_export "V3Glue.ChartInput" "strict_iso_of"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.V3Glue.ChartInput P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.AlgebraicGeometry.Scheme.IdealSheafData"

theorem solution
    {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N)
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (j : Fin 2)

    {R Xκ Bκ : Scheme.{0}} (c : R ⟶ Xκ) [IsClosedImmersion c] [IsIntegral R]
    (bcm : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (b : Bκ ⟶ C.B) (hP : IsPullback bcm p₂ C.πX b)
    (hξj : ξ j = (c ≫ bcm).base (genericPoint R))
    (hdesc : bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) = Set.range c.base)
    {pt : C.B} (hpt : IsClosed ({pt} : Set C.B)) (hfib : Set.range bcm.base = C.πX.base ⁻¹' {pt})
    (hcpt : ∀ r : R, (c ≫ bcm ≫ C.πX).base r = pt)

    {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n) [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))]
    (horient_fwd : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base →
      (y : X) ∈ Set.range (c ≫ bcm).base)
    (horient_conv : ∀ n (y : C.U n), (y : X) ∈ Set.range (c ≫ bcm).base →
      (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base)
    (hxim : ∀ n, C.x n ∈ Set.range (c ≫ bcm).base)

    (n₀ : N) {B₀ : Scheme.{0}} (i : B₀ ⟶ C.B) [Mono i] (a : Bκ ⟶ B₀) [Flat a] (hb : b = a ≫ i)
    (s₀ : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subscheme ⟶ B₀)
    (hsB : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX = s₀ ≫ i)
    (hGκ : IsReduced (pullback (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) b)) :
    ∃ e : pullback ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧
        e ≫ c ≫ bcm = pullback.fst _ _ ≫ (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR :=
  C.strict_iso_of hRF gRes hgRes ξ hξ j c bcm p₂ b hP hξj hdesc hpt hfib hcpt lam horient_fwd horient_conv hxim n₀ i a hb s₀ hsB hGκ

end S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform
end P2MW
export P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform (solution)
