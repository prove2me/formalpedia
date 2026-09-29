-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/66718c14-e4e2-5789-9671-345e6779b28b

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

namespace VCOAux
open HomogeneousLocalization

variable {T : Type u} [CommRing T]

lemma apply_sc_eq_of_eq (W : WeierstrassCurve.Projective T) {s : ProjModelRingCR W} {i : ℕ}
    (hs : s ∈ projModelGradingCR W i) (hi : 0 < i) (P : Section W) (χ : Away (projModelGradingCR W) s →+* T)
    (hχ : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ Proj.awayι (projModelGradingCR W) s hs hi) (t : T) :
    χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
  have h := P.2
  rw [hχ] at h
  simp only [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0)) ≫
      CommRingCat.ofHom (fromZeroRingHom (projModelGradingCR W) _) ≫ CommRingCat.ofHom χ) =
      Spec.map (𝟙 _) := by rw [Spec.map_id]; exact h
  have h3 := Spec.map_injective h2
  have h4 := congrArg (fun g : CommRingCat.of T ⟶ CommRingCat.of T => g.hom t) h3
  simpa using h4

section AwayHelpers

variable {A : Type u} [CommRing A] {σ' : Type*} [SetLike σ' A] [AddSubgroupClass σ' A]
  (𝒜 : ℕ → σ') [GradedRing 𝒜]

lemma Away.mk_add' {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (a b : A) (ha : a ∈ 𝒜 (n • d)) (hb : b ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n a ha + Away.mk 𝒜 hf n b hb = Away.mk 𝒜 hf n (a + b) (add_mem ha hb) := by
  ext
  simp only [val_add, Away.val_mk, Localization.add_mk_self]

lemma Away.mk_smul' {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (c a : A) (hc : c ∈ 𝒜 0) (ha : a ∈ 𝒜 (n • d))
    (hca : c * a ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n (c * a) hca = fromZeroRingHom 𝒜 _ ⟨c, hc⟩ * Away.mk 𝒜 hf n a ha := by
  ext
  simp only [val_mul, Away.val_mk]
  change Localization.mk (c * a) _ = Localization.mk c ⟨1, _⟩ * Localization.mk a _
  rw [Localization.mk_mul]
  congr 1
  exact Subtype.ext (one_mul _).symm

lemma Away.mk_self' {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (h : f ∈ 𝒜 (1 • d)) :
    Away.mk 𝒜 hf 1 f h = 1 := by
  ext
  simp only [val_one, Away.val_mk]
  convert Localization.mk_self (⟨f ^ 1, 1, rfl⟩ : Submonoid.powers f) using 2
  exact (pow_one f).symm

end AwayHelpers

section Chart

variable {T : Type u} [CommRing T] [IsLocalRing T]

set_option maxHeartbeats 6400000 in

theorem exists_chart_of_isVariableChangeHom
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hvc : IsVariableChangeHom W C φ)
    (P : Section W) (χ : OriginChartRing W →+* T) (hPχ : IsOriginChartSection P χ)
    (hz : originParam χ ∈ maximalIdeal T) (hw : originW χ ∈ maximalIdeal T)
    (P' : Section (C • W)) (hP' : P'.1 ≫ Proj.map φ hφ = P.1)
    (hYφ : φ (coord W 1) ∈ projModelGradingCR (C • W) 1)
    (χ₁ : Away (projModelGradingCR (C • W)) (φ (coord W 1)) →+* T)
    (hsec₁ : P'.1 = Spec.map (CommRingCat.ofHom χ₁) ≫ Proj.awayι (projModelGradingCR (C • W)) _ hYφ one_pos)
    (key₁ : χ₁.comp (Away.map φ (coord W 1)) = χ)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t)
    (hsc₁ : ∀ t : T, χ₁ (fromZeroRingHom (projModelGradingCR (C • W)) _
      (algebraMap T ((projModelGradingCR (C • W)) 0) t)) = t) :
    ∃ χ' : OriginChartRing (C • W) →+* T,
      IsOriginChartSection P' χ' ∧
      IsUnit (1 + C.s * (originParam χ - C.r * originW χ) + C.t * originW χ) ∧
      originParam χ' * (1 + C.s * (originParam χ - C.r * originW χ) + C.t * originW χ) =
        (C.u : T) * (originParam χ - C.r * originW χ) ∧
      originW χ' * (1 + C.s * (originParam χ - C.r * originW χ) + C.t * originW χ) =
        (C.u : T) ^ 3 * originW χ := by
  classical

  obtain ⟨hC, h0, h1, h2⟩ := hvc
  have hY : coord W 1 ∈ projModelGradingCR W 1 := coord_mem W 1
  have hY' : coord (C • W) 1 ∈ projModelGradingCR (C • W) 1 := coord_mem (C • W) 1
  have hX' : coord (C • W) 0 ∈ projModelGradingCR (C • W) (1 • 1) := by simpa using coord_mem (C • W) 0
  have hZ' : coord (C • W) 2 ∈ projModelGradingCR (C • W) (1 • 1) := by simpa using coord_mem (C • W) 2
  have hY'1 : coord (C • W) 1 ∈ projModelGradingCR (C • W) (1 • 1) := by simpa using hY'

  obtain ⟨a₁, ha₁⟩ : ∃ a : T, χ₁ (Away.mk _ hYφ 1 (coord (C • W) 0) hX') = a := ⟨_, rfl⟩
  obtain ⟨l₁, hl₁⟩ : ∃ a : T, χ₁ (Away.mk _ hYφ 1 (coord (C • W) 1) hY'1) = a := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ a : T, χ₁ (Away.mk _ hYφ 1 (coord (C • W) 2) hZ') = a := ⟨_, rfl⟩

  have hscal : ∀ (t : T) (ht : cls (C • W) (MvPolynomial.C t) ∈ projModelGradingCR (C • W) 0),
      χ₁ (fromZeroRingHom (projModelGradingCR (C • W)) _ ⟨cls (C • W) (MvPolynomial.C t), ht⟩) = t := by
    intro t ht
    convert hsc₁ t using 3
    rfl
  have hC0 : ∀ t : T, cls (C • W) (MvPolynomial.C t) ∈ projModelGradingCR (C • W) 0 := fun t ↦
    (algebraMap T ((projModelGradingCR (C • W)) 0) t).2
  have hs_u2 := hscal ((C.u : T) ^ 2) (hC0 _)
  have hs_r := hscal C.r (hC0 _)
  have hs_u3 := hscal ((C.u : T) ^ 3) (hC0 _)
  have hs_u2s := hscal ((C.u : T) ^ 2 * C.s) (hC0 _)
  have hs_t := hscal C.t (hC0 _)

  have hmapX : Away.map φ (coord W 1) (xOverY W) =
      Away.mk _ hYφ 1 (φ (coord W 0)) (by simpa using φ.2 (coord_mem W 0)) := by
    rw [xOverY, Away.map_mk]
  have hmapZ : Away.map φ (coord W 1) (zOverY W) =
      Away.mk _ hYφ 1 (φ (coord W 2)) (by simpa using φ.2 (coord_mem W 2)) := by
    rw [zOverY, Away.map_mk]
  have hmapY : Away.map φ (coord W 1) (Away.mk _ hY 1 (coord W 1) (by simpa using hY)) =
      Away.mk _ hYφ 1 (φ (coord W 1)) (by simpa using hYφ) := by
    rw [Away.map_mk]
  have eX : χ (xOverY W) = (C.u : T) ^ 2 * a₁ + C.r * c₁ := by
    rw [← key₁, RingHom.comp_apply, hmapX]
    have : Away.mk _ hYφ 1 (φ (coord W 0)) (by simpa using φ.2 (coord_mem W 0)) =
        fromZeroRingHom _ _ ⟨cls (C • W) (MvPolynomial.C ((C.u : T) ^ 2)), hC0 _⟩ *
            Away.mk _ hYφ 1 (coord (C • W) 0) hX' +
          fromZeroRingHom _ _ ⟨cls (C • W) (MvPolynomial.C C.r), hC0 _⟩ *
            Away.mk _ hYφ 1 (coord (C • W) 2) hZ' := by
      rw [← Away.mk_smul' _ hYφ 1 _ _ (hC0 _) hX', ← Away.mk_smul' _ hYφ 1 _ _ (hC0 _) hZ', Away.mk_add']
      · congr 1
      · have h := SetLike.mul_mem_graded (hC0 C.r) hZ'; rwa [_root_.zero_add] at h
      · have h := SetLike.mul_mem_graded (hC0 ((C.u : T) ^ 2)) hX'; rwa [_root_.zero_add] at h
    rw [this, map_add, map_mul χ₁, map_mul χ₁, hs_u2, hs_r, ha₁, hc₁]
  have eZ : χ (zOverY W) = c₁ := by
    rw [← key₁, RingHom.comp_apply, hmapZ, ← hc₁]
    congr 1
    all_goals (change Away.mk _ hYφ 1 (φ (cls W (MvPolynomial.X 2))) _ = _; congr 1)
  have eY : (1 : T) = (C.u : T) ^ 3 * l₁ + (C.u : T) ^ 2 * C.s * a₁ + C.t * c₁ := by
    have h1' : χ (Away.mk _ hY 1 (coord W 1) (by simpa using hY)) = 1 := by
      rw [Away.mk_self', map_one]
    rw [← h1', ← key₁, RingHom.comp_apply, hmapY]
    have : Away.mk _ hYφ 1 (φ (coord W 1)) (by simpa using hYφ) =
        fromZeroRingHom _ _ ⟨cls (C • W) (MvPolynomial.C ((C.u : T) ^ 3)), hC0 _⟩ *
            Away.mk _ hYφ 1 (coord (C • W) 1) hY'1 +
          fromZeroRingHom _ _ ⟨cls (C • W) (MvPolynomial.C ((C.u : T) ^ 2 * C.s)), hC0 _⟩ *
            Away.mk _ hYφ 1 (coord (C • W) 0) hX' +
          fromZeroRingHom _ _ ⟨cls (C • W) (MvPolynomial.C C.t), hC0 _⟩ *
            Away.mk _ hYφ 1 (coord (C • W) 2) hZ' := by
      rw [← Away.mk_smul' _ hYφ 1 _ _ (hC0 _) hY'1, ← Away.mk_smul' _ hYφ 1 _ _ (hC0 _) hX',
        ← Away.mk_smul' _ hYφ 1 _ _ (hC0 _) hZ', Away.mk_add', Away.mk_add']
      · congr 1
      · have h := SetLike.mul_mem_graded (hC0 C.t) hZ'; rwa [_root_.zero_add] at h
      · have h := SetLike.mul_mem_graded (hC0 ((C.u : T) ^ 2 * C.s)) hX'; rwa [_root_.zero_add] at h
      · have h := SetLike.mul_mem_graded (hC0 ((C.u : T) ^ 3)) hY'1; rwa [_root_.zero_add] at h
    rw [this, map_add, map_add, map_mul χ₁, map_mul χ₁, map_mul χ₁, hs_u3, hs_u2s, hs_t, ha₁, hl₁, hc₁]

  have hzdef : originParam χ = -((C.u : T) ^ 2 * a₁ + C.r * c₁) := by rw [originParam, eX]
  have hwdef : originW χ = -c₁ := by rw [originW, eZ]
  have hD : 1 + C.s * (originParam χ - C.r * originW χ) + C.t * originW χ = (C.u : T) ^ 3 * l₁ := by
    rw [hzdef, hwdef]; linear_combination eY
  have hDunit : IsUnit (1 + C.s * (originParam χ - C.r * originW χ) + C.t * originW χ) := by
    have hm : C.s * (originParam χ - C.r * originW χ) + C.t * originW χ ∈ maximalIdeal T :=
      add_mem (Ideal.mul_mem_left _ _ (sub_mem hz (Ideal.mul_mem_left _ _ hw))) (Ideal.mul_mem_left _ _ hw)
    by_contra hu
    have : (1 : T) + (C.s * (originParam χ - C.r * originW χ) + C.t * originW χ) ∈ maximalIdeal T := by
      rw [← add_assoc]; exact (IsLocalRing.mem_maximalIdeal _).mpr hu
    exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top
      ((Ideal.eq_top_iff_one _).mpr (by simpa using (Ideal.add_mem_iff_left _ hm).mp this))
  have hl₁unit : IsUnit l₁ := by
    have := hD ▸ hDunit
    exact isUnit_of_mul_isUnit_right this

  have hx : φ (coord W 1) * coord (C • W) 1 = φ (coord W 1) * coord (C • W) 1 := rfl
  have hx' : φ (coord W 1) * coord (C • W) 1 = coord (C • W) 1 * φ (coord W 1) := mul_comm _ _
  letI alg := (awayMap (projModelGradingCR (C • W)) hY' hx).toAlgebra
  haveI hloc := Away.isLocalization_mul hYφ hY' hx one_ne_zero
  have helem : Away.isLocalizationElem hYφ hY' = Away.mk _ hYφ 1 (coord (C • W) 1) hY'1 := by
    simp only [Away.isLocalizationElem, pow_one]
  have hunit : IsUnit (χ₁ (Away.isLocalizationElem hYφ hY')) := by rw [helem, hl₁]; exact hl₁unit
  let χx : Away (projModelGradingCR (C • W)) (φ (coord W 1) * coord (C • W) 1) →+* T :=
    IsLocalization.Away.lift (Away.isLocalizationElem hYφ hY') hunit
  have hχx : χx.comp (awayMap (projModelGradingCR (C • W)) hY' hx) = χ₁ :=
    IsLocalization.Away.lift_comp _ hunit
  let χ' : OriginChartRing (C • W) →+* T := χx.comp (awayMap (projModelGradingCR (C • W)) hYφ hx')
  refine ⟨χ', ?_, hDunit, ?_, ?_⟩
  ·
    show P'.1 = Spec.map (CommRingCat.ofHom χ') ≫ originChartι (C • W)
    rw [hsec₁, ← hχx]
    simp only [χ', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    change Spec.map (CommRingCat.ofHom χx) ≫ (Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR (C • W)) hY' hx)) ≫
        Proj.awayι (projModelGradingCR (C • W)) (φ (coord W 1)) hYφ one_pos) =
      Spec.map (CommRingCat.ofHom χx) ≫ (Spec.map (CommRingCat.ofHom (awayMap (projModelGradingCR (C • W)) hYφ hx')) ≫
        Proj.awayι (projModelGradingCR (C • W)) (coord (C • W) 1) hY' one_pos)
    rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]
  ·
    have hfrac : awayMap (projModelGradingCR (C • W)) hYφ hx' (xOverY (C • W)) *
        awayMap (projModelGradingCR (C • W)) hY' hx (Away.isLocalizationElem hYφ hY') =
        awayMap (projModelGradingCR (C • W)) hY' hx (Away.mk _ hYφ 1 (coord (C • W) 0) hX') := by
      rw [helem, xOverY]
      ext
      simp only [val_mul, awayMap_mk, Away.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
      ring
    have hA : χ' (xOverY (C • W)) * l₁ = a₁ := by
      have := congrArg χx hfrac
      rw [map_mul] at this
      have e1 : χx (awayMap _ hY' hx (Away.isLocalizationElem hYφ hY')) = l₁ := by
        rw [← RingHom.comp_apply, hχx, helem, hl₁]
      have e2 : χx (awayMap _ hY' hx (Away.mk _ hYφ 1 (coord (C • W) 0) hX')) = a₁ := by
        rw [← RingHom.comp_apply, hχx, ha₁]
      rw [e1, e2] at this
      exact this
    rw [hD, originParam, hzdef, hwdef]
    linear_combination (-(C.u : T) ^ 3) * hA
  ·
    have hfrac : awayMap (projModelGradingCR (C • W)) hYφ hx' (zOverY (C • W)) *
        awayMap (projModelGradingCR (C • W)) hY' hx (Away.isLocalizationElem hYφ hY') =
        awayMap (projModelGradingCR (C • W)) hY' hx (Away.mk _ hYφ 1 (coord (C • W) 2) hZ') := by
      rw [helem, zOverY]
      ext
      simp only [val_mul, awayMap_mk, Away.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
      ring
    have hCz : χ' (zOverY (C • W)) * l₁ = c₁ := by
      have := congrArg χx hfrac
      rw [map_mul] at this
      have e1 : χx (awayMap _ hY' hx (Away.isLocalizationElem hYφ hY')) = l₁ := by
        rw [← RingHom.comp_apply, hχx, helem, hl₁]
      have e2 : χx (awayMap _ hY' hx (Away.mk _ hYφ 1 (coord (C • W) 2) hZ')) = c₁ := by
        rw [← RingHom.comp_apply, hχx, hc₁]
      rw [e1, e2] at this
      exact this
    rw [hD, originW, hwdef]
    linear_combination (-(C.u : T) ^ 3) * hCz

end Chart

end VCOAux

open VCOAux HomogeneousLocalization in
set_option maxHeartbeats 6400000 in
theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hvc : IsVariableChangeHom W C φ)
    (P : Section W) (χ : OriginChartRing W →+* T) (hP : ReducesToOrigin P χ (maximalIdeal T))
    (P' : Section (C • W)) (hP' : P'.1 ≫ Proj.map φ hφ = P.1) :
    ∃ χ' : OriginChartRing (C • W) →+* T,
      ReducesToOrigin P' χ' (maximalIdeal T) ∧
      originParam χ' =
        (letI : WithIdeal T := ⟨maximalIdeal T⟩; FormalGroup.evalSeries (W.variableChangeSeries C) (originParam χ)) := by
  classical
  obtain ⟨hsec, hzI, hwI⟩ := hP

  have hY : coord W 1 ∈ projModelGradingCR W 1 := coord_mem W 1
  have hY' : coord (C • W) 1 ∈ projModelGradingCR (C • W) 1 := coord_mem (C • W) 1
  have hYφ : φ (coord W 1) ∈ projModelGradingCR (C • W) 1 := φ.2 hY

  have hrange : Set.range P'.1.base ⊆ Set.range (Proj.awayι (projModelGradingCR (C • W)) _ hYφ one_pos).base := by
    have hA : Set.range (originChartι W).base =
        ((Proj.basicOpen (projModelGradingCR W) (coord W 1)) : Set _) := by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    have hB : Set.range (Proj.awayι (projModelGradingCR (C • W)) _ hYφ one_pos).base =
        ((Proj.basicOpen (projModelGradingCR (C • W)) (φ (coord W 1))) : Set _) := by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    have hpre : SetLike.coe (Proj.map φ hφ ⁻¹ᵁ Proj.basicOpen (projModelGradingCR W) (coord W 1)) =
        SetLike.coe (Proj.basicOpen (projModelGradingCR (C • W)) (φ (coord W 1))) := by
      rw [Proj.map_preimage_basicOpen]
    rw [hB, ← hpre, Scheme.Hom.coe_preimage, ← hA]
    rintro _ ⟨x, rfl⟩
    rw [Set.mem_preimage]
    refine ⟨(Spec.map (CommRingCat.ofHom χ)) x, ?_⟩
    change (Spec.map (CommRingCat.ofHom χ) ≫ originChartι W) x = (P'.1 ≫ Proj.map φ hφ) x
    rw [hP', hsec]
  let g₁ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (Away (projModelGradingCR (C • W)) (φ (coord W 1)))) :=
    IsOpenImmersion.lift (Proj.awayι (projModelGradingCR (C • W)) _ hYφ one_pos) P'.1 hrange
  have hg₁ : g₁ ≫ Proj.awayι (projModelGradingCR (C • W)) _ hYφ one_pos = P'.1 := IsOpenImmersion.lift_fac _ _ hrange
  let χ₁ : Away (projModelGradingCR (C • W)) (φ (coord W 1)) →+* T :=
    ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom.comp g₁.appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of (Away (projModelGradingCR (C • W)) (φ (coord W 1))))).inv.hom
  have hχ₁ : Spec.map (CommRingCat.ofHom χ₁) = g₁ := by
    change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (Away (projModelGradingCR (C • W)) (φ (coord W 1))))).inv ≫
      g₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) = g₁
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← Scheme.isoSpec_Spec_hom,
      Category.assoc, Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have hsec₁ : P'.1 = Spec.map (CommRingCat.ofHom χ₁) ≫ Proj.awayι (projModelGradingCR (C • W)) _ hYφ one_pos := by
    rw [hχ₁, hg₁]

  have key₁ : χ₁.comp (Away.map φ (coord W 1)) = χ := by
    have h1 : Spec.map (CommRingCat.ofHom (χ₁.comp (Away.map φ (coord W 1)))) ≫ originChartι W =
        Spec.map (CommRingCat.ofHom χ) ≫ originChartι W := by
      simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      change Spec.map (CommRingCat.ofHom χ₁) ≫ (Spec.map (CommRingCat.ofHom (Away.map φ (coord W 1))) ≫
          Proj.awayι (projModelGradingCR W) (coord W 1) hY one_pos) = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W
      rw [← Proj.awayι_comp_map φ hφ one_pos (coord W 1) hY, ← Category.assoc, ← hsec₁, hP', hsec]
    have h2 := (cancel_mono (originChartι W)).mp h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)

  have hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t :=
    fun t => apply_sc_eq_of_eq W hY one_pos P χ hsec t
  have hsc₁ : ∀ t : T, χ₁ (fromZeroRingHom (projModelGradingCR (C • W)) _
      (algebraMap T ((projModelGradingCR (C • W)) 0) t)) = t :=
    fun t => apply_sc_eq_of_eq (C • W) hYφ one_pos P' χ₁ hsec₁ t

  obtain ⟨χ', hsec', hDunit, hzeq, hweq⟩ := exists_chart_of_isVariableChangeHom W C φ hφ hvc P χ hsec hzI hwI P' hP'
    hYφ χ₁ hsec₁ key₁ hsc hsc₁

  set z := originParam χ with hzdef
  set w := originW χ with hwdef
  set D := 1 + C.s * (z - C.r * w) + C.t * w with hDdef
  have hw_eval : w = (letI : WithIdeal T := ⟨maximalIdeal T⟩; FormalGroup.evalSeries W.formalW z) :=
    WeierstrassCurve.DrinfeldGlobal.originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection W P χ hsec hzI hwI
  obtain ⟨e, he, hepoly⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal T) z hzI
  have heC : ∀ a : T, e (PowerSeries.C a) = a := by
    intro a; have := hepoly (Polynomial.C a); rwa [Polynomial.coe_C, Polynomial.eval_C] at this
  have heX : e PowerSeries.X = z := by
    have := hepoly Polynomial.X; rwa [Polynomial.coe_X, Polynomial.eval_X] at this
  have heW : e W.formalW = w := by rw [← he, ← hw_eval]
  have heDn : e (W.variableChangeDenom C) = D := by
    simp only [WeierstrassCurve.variableChangeDenom, map_add, map_mul, map_sub, map_one, heC, heX, heW, hDdef]
  have heInv : e (PowerSeries.invOfUnit (W.variableChangeDenom C) 1) * D = 1 := by
    rw [← heDn, ← map_mul, mul_comm, PowerSeries.mul_invOfUnit _ _ (by
      rw [WeierstrassCurve.constantCoeff_variableChangeDenom]; rfl), map_one]
  have heψ : e (W.variableChangeSeries C) * D = (C.u : T) * (z - C.r * w) := by
    simp only [WeierstrassCurve.variableChangeSeries, map_mul, map_sub, heC, heX, heW]
    rw [mul_assoc, heInv, mul_one]
  refine ⟨χ', ⟨hsec', ?_, ?_⟩, ?_⟩
  ·
    have : originParam χ' = (C.u : T) * (z - C.r * w) * ↑(hDunit.unit⁻¹) := by
      rw [← hzeq, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hzI (Ideal.mul_mem_left _ _ hwI)))
  · have : originW χ' = (C.u : T) ^ 3 * w * ↑(hDunit.unit⁻¹) := by
      rw [← hweq, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hwI)
  ·
    change originParam χ' = (letI : WithIdeal T := ⟨maximalIdeal T⟩; FormalGroup.evalSeries (W.variableChangeSeries C) z)
    rw [he]
    have h1 : originParam χ' * D = e (W.variableChangeSeries C) * D := by rw [hzeq, heψ]
    exact hDunit.mul_right_cancel h1

end S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom (solution)
