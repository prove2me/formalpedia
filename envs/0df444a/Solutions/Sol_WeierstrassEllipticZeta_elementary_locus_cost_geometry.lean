-- Prove2me | solution 1 for WeierstrassEllipticZeta.elementary_locus_cost_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T15:45:42.755352+00:00
-- url     : https://prove2.me/submissions/a1ddc9c0-ebc0-480a-a78b-23bf6daec857

import Definitions.Def_WeierstrassEllipticZeta_ElementaryLoci
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

noncomputable section
open TranscendenceTheory
open scoped Classical
namespace WeierstrassEllipticZeta

private lemma directions_affine_coset
    (V : Submodule ℂ (Fin 3 → ℂ)) (r : Fin 3 → ℂ) :
    linearTranslationDirections ((fun v => r + v) '' (V : Set (Fin 3 → ℂ))) = V := by
  ext v
  constructor
  · intro hv
    change ∀ t : ℂ, ∀ w ∈ (fun v => r + v) '' (V : Set (Fin 3 → ℂ)),
      w + t • v ∈ (fun v => r + v) '' (V : Set (Fin 3 → ℂ)) at hv
    have hr : r ∈ (fun v => r + v) '' (V : Set (Fin 3 → ℂ)) :=
      ⟨0, V.zero_mem, add_zero r⟩
    have hrv := hv 1 r hr
    simp only [one_smul] at hrv
    obtain ⟨u, hu, heq⟩ := hrv
    exact (add_left_cancel heq) ▸ hu
  · intro hv
    change ∀ t : ℂ, ∀ w ∈ (fun v => r + v) '' (V : Set (Fin 3 → ℂ)),
      w + t • v ∈ (fun v => r + v) '' (V : Set (Fin 3 → ℂ))
    rintro t w ⟨u, hu, rfl⟩
    exact ⟨u + t • v, V.add_mem hu (V.smul_mem t hv), (add_assoc r u (t • v)).symm⟩

private lemma elementary_directions (shape : ElementaryLocusShape) (r : Fin 3 → ℂ) :
    linearTranslationDirections (elementaryLocus shape r) = elementaryDirections shape :=
  directions_affine_coset _ _

private lemma elementary_nonempty (shape : ElementaryLocusShape) (r : Fin 3 → ℂ) :
    (elementaryLocus shape r).Nonempty :=
  ⟨r, 0, (elementaryDirections shape).zero_mem, add_zero r⟩

private lemma line_mem (α : ℂ) (v : Fin 3 → ℂ) :
    v ∈ elementaryDirections (.line α) ↔ v 1 = 0 ∧ v 2 = α * v 0 := by
  simp [elementaryDirections, sub_eq_zero]

private lemma fibre_mem (v : Fin 3 → ℂ) :
    v ∈ elementaryDirections .fibre ↔ v 1 = 0 := by
  rfl

private lemma elementary_degree (shape : ElementaryLocusShape) (r : Fin 3 → ℂ) (m : ℕ) :
    (if ∀ v ∈ linearTranslationDirections (elementaryLocus shape r), v 0 = 0
      then m else 0) = elementaryDegree shape m := by
  rw [elementary_directions]
  cases shape with
  | point => simp [elementaryDirections, elementaryDegree]
  | line α =>
    have h : ¬ ∀ v ∈ elementaryDirections (.line α), v 0 = 0 := by
      intro h
      have := h ![1, 0, α] ((line_mem α _).2 (by simp))
      simpa using this
    simp [h, elementaryDegree]
  | fibre =>
    have h : ¬ ∀ v ∈ elementaryDirections .fibre, v 0 = 0 := by
      intro h
      have := h ![1, 0, 0] ((fibre_mem _).2 (by simp))
      simpa using this
    simp [h, elementaryDegree]

private lemma mem_resonant (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (α z : ℂ) :
    z ∈ resonantPeriods Λ η α ↔ ∃ hz : z ∈ Λ, η ⟨z, hz⟩ = α * z := by
  constructor
  · rintro ⟨ω, hω, hωz⟩
    change η ω - α * (ω : ℂ) = 0 at hω
    change (ω : ℂ) = z at hωz
    subst z
    exact ⟨ω.property, sub_eq_zero.mp hω⟩
  · rintro ⟨hz, heq⟩
    exact ⟨⟨z, hz⟩, by change η ⟨z, hz⟩ - α * z = 0; rw [heq, sub_self], rfl⟩

private lemma curve_mem_image_iff
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (W : Set (Fin 3 → ℂ)) (z : ℂ) :
    extensionCurve Λ η z ∈ linearTranslationImage Λ η W ↔
      ∃ v ∈ linearTranslationDirections W, v 0 = z ∧
        (z - v 1, -v 2) ∈ extensionPeriodGraph Λ η := by
  constructor
  · rintro ⟨v, hv, heq⟩
    have h0 : v 0 = z := congrArg Prod.fst heq
    have hq : (extensionPeriodGraph Λ η).mkQ (v 1, v 2) =
        (extensionPeriodGraph Λ η).mkQ (z, 0) := congrArg Prod.snd heq
    have hk : (extensionPeriodGraph Λ η).mkQ ((z, 0) - (v 1, v 2)) = 0 := by
      rw [map_sub, hq, sub_self]
    refine ⟨v, hv, h0, ?_⟩
    simpa using (Submodule.Quotient.mk_eq_zero _).mp hk
  · rintro ⟨v, hv, h0, hk⟩
    refine ⟨v, hv, ?_⟩
    apply Prod.ext
    · exact h0
    · change (extensionPeriodGraph Λ η).mkQ (v 1, v 2) =
        (extensionPeriodGraph Λ η).mkQ (z, 0)
      have hz : (extensionPeriodGraph Λ η).mkQ ((z, 0) - (v 1, v 2)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using hk)
      exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm

private lemma elementary_curve_kernel
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (shape : ElementaryLocusShape) (r : Fin 3 → ℂ) :
    LinearMap.ker ((linearTranslationImage Λ η (elementaryLocus shape r)).mkQ.comp
      (extensionCurve Λ η)) = elementaryPeriodKernel Λ η shape := by
  ext z
  change (linearTranslationImage Λ η (elementaryLocus shape r)).mkQ
      (extensionCurve Λ η z) = 0 ↔ z ∈ elementaryPeriodKernel Λ η shape
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, curve_mem_image_iff,
    elementary_directions]
  cases shape with
  | point =>
    simp [elementaryDirections, elementaryPeriodKernel, eq_comm]
    rintro rfl
    exact (extensionPeriodGraph Λ η).zero_mem
  | line α =>
    rw [show elementaryPeriodKernel Λ η (.line α) = resonantPeriods Λ η α from rfl,
      mem_resonant]
    constructor
    · rintro ⟨v, hv, hv0, ω, hω⟩
      obtain ⟨hv1, hv2⟩ := (line_mem α v).1 hv
      have he1 : (ω : ℂ) = z := by simpa [hv1] using congrArg Prod.fst hω
      have he2 : η ω = α * z := by
        have := congrArg Prod.snd hω
        simpa [hv2, hv0] using this
      refine ⟨he1 ▸ ω.property, ?_⟩
      convert he2 using 1
      congr 1
      exact Subtype.ext he1.symm
    · rintro ⟨hz, heq⟩
      refine ⟨![z, 0, α * z], (line_mem α _).2 (by simp), by simp, ⟨z, hz⟩, ?_⟩
      ext <;> simp [heq]
  | fibre =>
    change (∃ v ∈ elementaryDirections .fibre, v 0 = z ∧
      (z - v 1, -v 2) ∈ extensionPeriodGraph Λ η) ↔ z ∈ Λ
    constructor
    · rintro ⟨v, hv, hv0, ω, hω⟩
      have hv1 := (fibre_mem v).1 hv
      have he1 : (ω : ℂ) = z := by simpa [hv1] using congrArg Prod.fst hω
      exact he1 ▸ ω.property
    · intro hz
      refine ⟨![z, 0, η ⟨z, hz⟩], (fibre_mem _).2 (by simp), by simp, ⟨z, hz⟩, ?_⟩
      ext <;> simp

private lemma image_card_kernel {R A B : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (F : A →ₗ[R] B) (X : Finset A) :
    (X.image F).card = (X.image F.ker.mkQ).card := by
  let e : A ⧸ F.ker →ₗ[R] B := F.range.subtype.comp F.quotKerEquivRange.toLinearMap
  have he : Function.Injective e :=
    Subtype.val_injective.comp F.quotKerEquivRange.injective
  have hF : F = e.comp F.ker.mkQ := by
    ext x
    exact (F.quotKerEquivRange_apply_mk x).symm
  have himages : X.image F = (X.image F.ker.mkQ).image e := by
    rw [Finset.image_image]
    congr 1
  rw [himages, Finset.card_image_of_injective _ he]

private lemma elementary_card (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (shape : ElementaryLocusShape) (r : Fin 3 → ℂ) (X : Finset ℂ) :
    (X.image (fun z => (linearTranslationImage Λ η (elementaryLocus shape r)).mkQ
      (extensionCurve Λ η z))).card =
        (X.image (elementaryPeriodKernel Λ η shape).mkQ).card := by
  have h := image_card_kernel
    ((linearTranslationImage Λ η (elementaryLocus shape r)).mkQ.comp (extensionCurve Λ η)) X
  rw [elementary_curve_kernel] at h
  exact h

private lemma projection_directions
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (p : ℂ) (hp : p ∉ Λ)
    (W : Set (Fin 3 → ℂ))
    (hH : linearTranslationImage Λ η W ≤ LinearMap.ker (extensionAdditiveProjection Λ η) ∨
      linearTranslationImage Λ η W ≤ LinearMap.ker (extensionEllipticProjection Λ η)) :
    (∀ v ∈ linearTranslationDirections W, v 0 = 0) ∨
      (∀ v ∈ linearTranslationDirections W, v 1 = 0) := by
  rcases hH with hH | hH
  · left
    intro v hv
    exact hH ⟨v, hv, rfl⟩
  · right
    intro v hv
    by_contra hne
    have hv' := (linearTranslationDirections W).smul_mem (p / v 1) hv
    have hmem : extensionCoveringMap Λ η ((p / v 1) • v) ∈
        linearTranslationImage Λ η W := ⟨_, hv', rfl⟩
    have hh := hH hmem
    change Λ.mkQ ((p / v 1) * v 1) = 0 at hh
    rw [div_mul_cancel₀ _ hne] at hh
    exact hp ((Submodule.Quotient.mk_eq_zero _).mp hh)

private lemma plane_subspace_normal_form (V : Submodule ℂ (Fin 3 → ℂ))
    (h1 : ∀ v ∈ V, v 1 = 0) (h0 : ¬ ∀ v ∈ V, v 0 = 0) :
    ∃ shape : ElementaryLocusShape, V = elementaryDirections shape := by
  push Not at h0
  obtain ⟨v, hv, hv0⟩ := h0
  let α := v 2 / v 0
  have hw : ![1, 0, α] ∈ V := by
    have hh := V.smul_mem (v 0)⁻¹ hv
    convert hh using 1
    ext i
    fin_cases i <;> simp [α, h1 v hv, hv0, div_eq_mul_inv, mul_comm]
  by_cases he : ![0, 0, 1] ∈ V
  · refine ⟨.fibre, le_antisymm ?_ ?_⟩
    · intro u hu
      exact (fibre_mem u).2 (h1 u hu)
    · intro u hu
      have hu1 := (fibre_mem u).1 hu
      have hh := V.add_mem (V.smul_mem (u 0) hw) (V.smul_mem (u 2 - α * u 0) he)
      convert hh using 1
      ext i
      fin_cases i <;> simp [hu1] <;> ring
  · refine ⟨.line α, le_antisymm ?_ ?_⟩
    · intro u hu
      refine (line_mem α u).2 ⟨h1 u hu, ?_⟩
      by_contra hneq
      have hd : u 2 - α * u 0 ≠ 0 := sub_ne_zero.mpr hneq
      have hh := V.smul_mem (u 2 - α * u 0)⁻¹ (V.sub_mem hu (V.smul_mem (u 0) hw))
      apply he
      convert hh using 1
      ext i
      fin_cases i
      · change 0 = (u 2 - α * u 0)⁻¹ * (u 0 - u 0 * 1)
        simp
      · change 0 = (u 2 - α * u 0)⁻¹ * (u 1 - u 0 * 0)
        simp [h1 u hu]
      · change 1 = (u 2 - α * u 0)⁻¹ * (u 2 - u 0 * α)
        rw [mul_comm (u 0) α, inv_mul_cancel₀ hd]
    · intro u hu
      obtain ⟨hu1, hu2⟩ := (line_mem α u).1 hu
      have hh := V.smul_mem (u 0) hw
      convert hh using 1
      ext i
      fin_cases i <;> simp [hu1, hu2, mul_comm]

private lemma additive_image_card
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (W : Set (Fin 3 → ℂ))
    (h0 : ∀ v ∈ linearTranslationDirections W, v 0 = 0) (X : Finset ℂ) :
    (X.image (fun z => (linearTranslationImage Λ η W).mkQ
      (extensionCurve Λ η z))).card = X.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  dsimp only at hxy
  have hzero : (linearTranslationImage Λ η W).mkQ (extensionCurve Λ η (x - y)) = 0 := by
    rw [map_sub, map_sub, hxy, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hzero
  obtain ⟨v, hv, hv0, _⟩ := (curve_mem_image_iff Λ η W (x - y)).1 hmem
  exact sub_eq_zero.mp (hv0.symm.trans (h0 v hv))

private lemma elementary_replacement
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (W : Set (Fin 3 → ℂ))
    (hW : W.Nonempty)
    (hprofile : (∀ v ∈ linearTranslationDirections W, v 0 = 0) ∨
      (∀ v ∈ linearTranslationDirections W, v 1 = 0)) :
    ∃ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
      elementaryLocus shape r ⊆ W ∧
      (∀ m : ℕ, elementaryDegree shape m =
        if ∀ v ∈ linearTranslationDirections W, v 0 = 0 then m else 0) ∧
      ∀ X : Finset ℂ, (X.image (elementaryPeriodKernel Λ η shape).mkQ).card =
        (X.image (fun z => (linearTranslationImage Λ η W).mkQ (extensionCurve Λ η z))).card := by
  obtain ⟨r, hr⟩ := hW
  by_cases h0 : ∀ v ∈ linearTranslationDirections W, v 0 = 0
  · refine ⟨.point, r, ?_, ?_, ?_⟩
    · rintro w ⟨v, hv, rfl⟩
      have hv0 : v = 0 := hv
      simpa [hv0] using hr
    · intro m
      exact (if_pos h0).symm
    · intro X
      rw [← elementary_card Λ η .point r X, additive_image_card Λ η W h0 X]
      apply additive_image_card
      intro v hv
      rw [elementary_directions] at hv
      have hv0 : v = 0 := hv
      simp [hv0]
  · have h1 : ∀ v ∈ linearTranslationDirections W, v 1 = 0 :=
      hprofile.resolve_left h0
    obtain ⟨shape, hshape⟩ := plane_subspace_normal_form (linearTranslationDirections W) h1 h0
    have hdirs : linearTranslationDirections (elementaryLocus shape r) =
        linearTranslationDirections W := (elementary_directions shape r).trans hshape.symm
    refine ⟨shape, r, ?_, ?_, ?_⟩
    · rintro w ⟨v, hv, rfl⟩
      rw [← hshape] at hv
      change ∀ t : ℂ, ∀ w ∈ W, w + t • v ∈ W at hv
      simpa using hv 1 r hr
    · intro m
      rw [← elementary_degree shape r m, hdirs]
    · intro X
      rw [← elementary_card Λ η shape r X]
      have himage : linearTranslationImage Λ η (elementaryLocus shape r) =
          linearTranslationImage Λ η W := by
        unfold linearTranslationImage
        rw [hdirs]
      rw [himage]


end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (p : ℂ) (hp : p ∉ Λ) :
    (∀ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
      (elementaryLocus shape r).Nonempty ∧
      linearTranslationDirections (elementaryLocus shape r) = elementaryDirections shape ∧
      (∀ m : ℕ,
        (if ∀ v ∈ linearTranslationDirections (elementaryLocus shape r), v 0 = 0
          then m else 0) = elementaryDegree shape m) ∧
      LinearMap.ker ((linearTranslationImage Λ η (elementaryLocus shape r)).mkQ.comp
        (extensionCurve Λ η)) = elementaryPeriodKernel Λ η shape ∧
      ∀ X : Finset ℂ,
        (X.image (fun z => (linearTranslationImage Λ η (elementaryLocus shape r)).mkQ
          (extensionCurve Λ η z))).card =
            (X.image (elementaryPeriodKernel Λ η shape).mkQ).card) ∧
    (∀ (W : Set (Fin 3 → ℂ)), W.Nonempty →
      (linearTranslationImage Λ η W ≤ LinearMap.ker (extensionAdditiveProjection Λ η) ∨
        linearTranslationImage Λ η W ≤ LinearMap.ker (extensionEllipticProjection Λ η)) →
      ∃ (shape : ElementaryLocusShape) (r : Fin 3 → ℂ),
        elementaryLocus shape r ⊆ W ∧
        (∀ m : ℕ, elementaryDegree shape m =
          if ∀ v ∈ linearTranslationDirections W, v 0 = 0 then m else 0) ∧
        ∀ X : Finset ℂ, (X.image (elementaryPeriodKernel Λ η shape).mkQ).card =
          (X.image (fun z => (linearTranslationImage Λ η W).mkQ
            (extensionCurve Λ η z))).card) := by
  constructor
  · intro shape r
    exact ⟨elementary_nonempty shape r, elementary_directions shape r,
      elementary_degree shape r, elementary_curve_kernel Λ η shape r,
      elementary_card Λ η shape r⟩
  · intro W hW hH
    exact elementary_replacement Λ η W hW (projection_directions Λ η p hp W hH)
