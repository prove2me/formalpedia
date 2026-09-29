-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/21aa4229-9c24-55db-a2f3-e2ca9f93fd3b

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_of_nsmul_eq_one_of_not_reducesToOrigin
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_or_exists_reducesToOrigin
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra WeierstrassCurve.DrinfeldGlobal

namespace ConstSecAsm

section KHalf

variable {T : Type} [CommRing T] {E₁ E₂ : Scheme} {s₁ : E₁ ⟶ Spec (CommRingCat.of T)} {s₂ : E₂ ⟶ Spec (CommRingCat.of T)}

theorem nsmul_comp_eq_of_hom (G₁ : RelativeGroupLaw T s₁) (G₂ : RelativeGroupLaw T s₂)
    (h : E₁ ⟶ E₂) (hh : h ≫ s₂ = s₁)
    (hhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t s₁),
      (⟨(G₁.mul t x y).1 ≫ h, by rw [Category.assoc, hh]; exact (G₁.mul t x y).2⟩ : SchemeHomOver t s₂) =
        G₂.mul t ⟨x.1 ≫ h, by rw [Category.assoc, hh]; exact x.2⟩ ⟨y.1 ≫ h, by rw [Category.assoc, hh]; exact y.2⟩)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t s₁) (n : ℕ) :
    (⟨(G₁.nsmul t n x).1 ≫ h, by rw [Category.assoc, hh]; exact (G₁.nsmul t n x).2⟩ : SchemeHomOver t s₂) =
      G₂.nsmul t n ⟨x.1 ≫ h, by rw [Category.assoc, hh]; exact x.2⟩ := by
  induction n with
  | zero =>

    set e : SchemeHomOver t s₂ := ⟨(G₁.one t).1 ≫ h, by rw [Category.assoc, hh]; exact (G₁.one t).2⟩ with hedef
    have h11 := hhom t (G₁.one t) (G₁.one t)
    have hee : G₂.mul t e e = e := by
      rw [hedef, ← h11]
      exact Subtype.ext (by simp only [G₁.one_mul])
    letI := G₂.pointGroup t
    have he1 : e = G₂.one t := mul_eq_left.mp hee
    show e = G₂.one t
    exact he1
  | succ n ih =>
    exact (hhom t (G₁.nsmul t n x) x).trans (by rw [ih]; rfl)

theorem nsmul_comp_eq_one_of_hom (G₁ : RelativeGroupLaw T s₁) (G₂ : RelativeGroupLaw T s₂)
    (h : E₁ ⟶ E₂) (hh : h ≫ s₂ = s₁)
    (hhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t s₁),
      (⟨(G₁.mul t x y).1 ≫ h, by rw [Category.assoc, hh]; exact (G₁.mul t x y).2⟩ : SchemeHomOver t s₂) =
        G₂.mul t ⟨x.1 ≫ h, by rw [Category.assoc, hh]; exact x.2⟩ ⟨y.1 ≫ h, by rw [Category.assoc, hh]; exact y.2⟩)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t s₁)
    (hx : (⟨x.1 ≫ h, by rw [Category.assoc, hh]; exact x.2⟩ : SchemeHomOver t s₂) = G₂.one t) (n : ℕ) :
    (⟨(G₁.nsmul t n x).1 ≫ h, by rw [Category.assoc, hh]; exact (G₁.nsmul t n x).2⟩ : SchemeHomOver t s₂) =
      G₂.one t := by
  rw [nsmul_comp_eq_of_hom G₁ G₂ h hh hhom t x n, hx, G₂.nsmul_unit]

theorem comp_schemeNsmul_eq (G : RelativeGroupLaw T s₁) {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T))
    (x : SchemeHomOver t s₁) (n : ℕ) :
    x.1 ≫ G.schemeNsmul n = (G.nsmul t n x).1 := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := s₁)) = x :=
    Subtype.ext (Category.comp_id _)
  have := G.nsmul_natural s₁ t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at this
  exact congrArg Subtype.val this

theorem comp_eq_comp_one_of_forall_nsmul (Gq : RelativeGroupLaw T s₁) (G' : RelativeGroupLaw T s₂)
    (P : SchemeHomOver (𝟙 _) s₁) {K : Scheme} (ι : K ⟶ E₁)
    (hagree : ∀ (X : Scheme) (f g : E₁ ⟶ X),
      (∀ i : ℕ, (Gq.nsmul (𝟙 _) i P).1 ≫ f = (Gq.nsmul (𝟙 _) i P).1 ≫ g) → ι ≫ f = ι ≫ g)
    (h : E₁ ⟶ E₂) (hall : ∀ i : ℕ, (Gq.nsmul (𝟙 _) i P).1 ≫ h = (G'.one (𝟙 _)).1) :
    ι ≫ h = (ι ≫ s₁) ≫ (G'.one (𝟙 _)).1 := by
  rw [Category.assoc]
  apply hagree
  intro i
  rw [hall i, ← Category.assoc, (Gq.nsmul (𝟙 _) i P).2, Category.id_comp]

theorem comp_eq_comp_one_of_hom_of_comp_eq_one (Gq : RelativeGroupLaw T s₁) (G' : RelativeGroupLaw T s₂)
    (P : SchemeHomOver (𝟙 _) s₁) {K : Scheme} (ι : K ⟶ E₁)
    (hagree : ∀ (X : Scheme) (f g : E₁ ⟶ X),
      (∀ i : ℕ, (Gq.nsmul (𝟙 _) i P).1 ≫ f = (Gq.nsmul (𝟙 _) i P).1 ≫ g) → ι ≫ f = ι ≫ g)
    (h : E₁ ⟶ E₂) (hh : h ≫ s₂ = s₁)
    (hhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t s₁),
      (⟨(Gq.mul t x y).1 ≫ h, by rw [Category.assoc, hh]; exact (Gq.mul t x y).2⟩ : SchemeHomOver t s₂) =
        G'.mul t ⟨x.1 ≫ h, by rw [Category.assoc, hh]; exact x.2⟩ ⟨y.1 ≫ h, by rw [Category.assoc, hh]; exact y.2⟩)
    (hP : (⟨P.1 ≫ h, by rw [Category.assoc, hh]; exact P.2⟩ : SchemeHomOver (𝟙 _) s₂) = G'.one (𝟙 _)) :
    ι ≫ h = (ι ≫ s₁) ≫ (G'.one (𝟙 _)).1 :=
  comp_eq_comp_one_of_forall_nsmul Gq G' P ι hagree h fun i =>
    congrArg Subtype.val (nsmul_comp_eq_one_of_hom Gq G' h hh hhom (𝟙 _) P hP i)

end KHalf

section SectionHalf

attribute [local instance] MvPolynomial.gradedAlgebra

open IsLocalRing HomogeneousLocalization in

theorem not_reducesToOrigin_of_isSectionThrough
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve.Projective T) (S : Section W)
    {x y : T} (hS : IsSectionThrough S x y) (χ : OriginChartRing W →+* T) :
    ¬ ReducesToOrigin S χ (maximalIdeal T) := by
  classical
  rintro ⟨hχ, -, hw⟩
  obtain ⟨ρ, hρ, -, -⟩ := hS
  have hρ' : S.1 = Spec.map (CommRingCat.ofHom ρ) ≫ zChartι W := hρ
  have hχ' : S.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W := hχ

  have hZ : S.1 (closedPoint T) ∈ Proj.basicOpen (projModelGradingCR W) (coord W 2) := by
    rw [← Proj.opensRange_awayι _ (coord W 2) (coord_mem W 2) one_pos, Scheme.Hom.mem_opensRange]
    exact ⟨Spec.map (CommRingCat.ofHom ρ) (closedPoint T), by rw [← Scheme.Hom.comp_apply, ← hρ']⟩

  have hunit : χ (zOverY W) ∉ maximalIdeal T := by
    rw [hχ', Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage,
      Proj.awayι_preimage_basicOpen (projModelGradingCR W) (f_deg := coord_mem W 1) (hm := one_pos)
        (g_deg := coord_mem W 2) (hm' := one_pos)] at hZ
    change PrimeSpectrum.comap χ (closedPoint T) ∈
      PrimeSpectrum.basicOpen (Away.isLocalizationElem (coord_mem W 1) (coord_mem W 2)) at hZ
    rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hZ
    have he : Away.isLocalizationElem (coord_mem W 1) (coord_mem W 2) = zOverY W := by
      apply HomogeneousLocalization.val_injective
      simp only [Away.isLocalizationElem, zOverY, Away.val_mk, pow_one]
    rwa [he] at hZ
  apply hunit
  have : -(χ (zOverY W)) ∈ maximalIdeal T := hw
  simpa using (maximalIdeal T).neg_mem this

theorem snd_pow_dualNumber {k : Type} [Field k] (z : DualNumber k) (n : ℕ) :
    TrivSqZeroExt.snd (z ^ n) = (n : k) * z.fst ^ (n - 1) * z.snd := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, DualNumber.snd_mul, ih, TrivSqZeroExt.fst_pow]
    rcases n with _ | n
    · simp
    · simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ]
      ring

theorem pow_char_eq_algebraMap {k : Type} [Field k] (q : ℕ) [hq : Fact q.Prime] [CharP k q] (z : DualNumber k) :
    z ^ q = algebraMap k (DualNumber k) (z.fst ^ q) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_pow, TrivSqZeroExt.algebraMap_eq_inl]; rfl
  · rw [snd_pow_dualNumber, CharP.cast_eq_zero, zero_mul, zero_mul]; simp

end SectionHalf

end ConstSecAsm

section LemmaR
open IsLocalRing HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace OriginReductionAux

theorem exists_originChartι_comp_projMap
    {T T' : Type} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ) :
    ∃ a : OriginChartRing W →+* OriginChartRing (W.map f),
      originChartι (W.map f) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ originChartι W ∧
      a (xOverY W) = xOverY (W.map f) ∧ a (zOverY W) = zOverY (W.map f) := by
  obtain ⟨-, hX⟩ := hcoef
  have key : ∀ (s : ProjModelRingCR (W.map f)) (hs : s ∈ projModelGradingCR (W.map f) 1)
      (e : φ (coord W 1) = s),
      ∃ a : OriginChartRing W →+* Away (projModelGradingCR (W.map f)) s,
        Proj.awayι (projModelGradingCR (W.map f)) s hs one_pos ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom a) ≫ originChartι W ∧
        a (xOverY W) = Away.mk (projModelGradingCR (W.map f)) hs 1 (coord (W.map f) 0)
          (by simpa using coord_mem (W.map f) 0) ∧
        a (zOverY W) = Away.mk (projModelGradingCR (W.map f)) hs 1 (coord (W.map f) 2)
          (by simpa using coord_mem (W.map f) 2) := by
    intro s hs e
    subst e
    refine ⟨Away.map φ (coord W 1), ?_, ?_, ?_⟩
    · exact Proj.awayι_comp_map φ hφ one_pos (coord W 1) (coord_mem W 1)
    · show Away.map φ (coord W 1) (Away.mk _ (coord_mem W 1) 1 (coord W 0) _) = _
      rw [Away.map_mk]
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk]
      congr 1
      · exact hX 0
    · show Away.map φ (coord W 1) (Away.mk _ (coord_mem W 1) 1 (coord W 2) _) = _
      rw [Away.map_mk]
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk]
      congr 1
      · exact hX 2
  exact key (coord (W.map f) 1) (coord_mem (W.map f) 1) (hX 1)

theorem originChartι_comp_projModelStrCR {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T) :
    originChartι W ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom ((fromZeroRingHom (projModelGradingCR W) _).comp
        (algebraMap T ((projModelGradingCR W) 0)))) := by
  show Proj.awayι (projModelGradingCR W) (coord W 1) (coord_mem W 1) one_pos ≫ projModelStrCR W = _
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem comp_scalar_eq_id {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T)
    (s : Spec (CommRingCat.of T) ⟶ projModelCR W) (hs : s ≫ projModelStrCR W = 𝟙 _)
    (χ : OriginChartRing W →+* T) (hχ : s = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W) :
    χ.comp ((fromZeroRingHom (projModelGradingCR W) _).comp (algebraMap T ((projModelGradingCR W) 0))) =
      RingHom.id T := by
  have e : Spec.map (CommRingCat.ofHom (χ.comp ((fromZeroRingHom (projModelGradingCR W) _).comp
      (algebraMap T ((projModelGradingCR W) 0))))) = Spec.map (CommRingCat.ofHom (RingHom.id T)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← originChartι_comp_projModelStrCR, ← Category.assoc, ← hχ, hs,
      CommRingCat.ofHom_id, Spec.map_id]
  have h := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  simpa only [CommRingCat.hom_ofHom] using h

theorem comp_eq_comp_of_square {X X' : Scheme} {R R' T T' : Type} [CommRing R] [CommRing R'] [CommRing T]
    [CommRing T']
    (c : Spec (CommRingCat.of R) ⟶ X) (c' : Spec (CommRingCat.of R') ⟶ X') (Pr : X' ⟶ X)
    (p : X ⟶ Spec (CommRingCat.of T)) (p' : X' ⟶ Spec (CommRingCat.of T')) (f : T →+* T')
    (hsq : Pr ≫ p = p' ≫ Spec.map (CommRingCat.ofHom f))
    (a : R →+* R') (ha : c' ≫ Pr = Spec.map (CommRingCat.ofHom a) ≫ c)
    (s : T →+* R) (hs : c ≫ p = Spec.map (CommRingCat.ofHom s))
    (s' : T' →+* R') (hs' : c' ≫ p' = Spec.map (CommRingCat.ofHom s')) :
    a.comp s = s'.comp f := by
  have e : Spec.map (CommRingCat.ofHom (a.comp s)) = Spec.map (CommRingCat.ofHom (s'.comp f)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp, ← hs, ← hs',
      ← Category.assoc, ← ha, Category.assoc, hsq, Category.assoc]
  have h := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  simpa only [CommRingCat.hom_ofHom] using h

end OriginReductionAux

open OriginReductionAux

theorem specMap_fstHom_comp_projMap_eq_one_of_reducesToOrigin
    {B : Type} [CommRing B] (V : WeierstrassCurve B) (k : Type) [Field k] (β : B →+* DualNumber k)
    (φ : projModelGradingCR V.toProjective →+*ᵍ projModelGradingCR (V.map β).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map β).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V.toProjective)).map φ)
    (hcoef : IsCoefficientHom V.toProjective β φ)
    (GB : RelativeGroupLaw B (projModelStrCR V.toProjective))
    (G : RelativeGroupLaw (DualNumber k) (projModelStrCR (V.map β).toProjective))
    (hGB : ∃ χ : OriginChartRing V.toProjective →+* B,
      IsOriginChartSection (GB.one (𝟙 _)) χ ∧ χ (xOverY V.toProjective) = 0 ∧ χ (zOverY V.toProjective) = 0)
    (hG : ∃ χ : OriginChartRing (V.map β).toProjective →+* DualNumber k,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY (V.map β).toProjective) = 0 ∧ χ (zOverY (V.map β).toProjective) = 0)
    (S : Section (V.map β).toProjective) (χ : OriginChartRing (V.map β).toProjective →+* DualNumber k)
    (hS : ReducesToOrigin S χ (maximalIdeal (DualNumber k))) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ S.1 ≫ Proj.map φ hφ =
      (GB.one (Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)))).1 := by
  classical
  obtain ⟨hχ, hx, hz⟩ := hS
  obtain ⟨χB, hχB, hχBx, hχBz⟩ := hGB
  have hχ' : S.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι (V.map β).toProjective := hχ
  have hχB' : (GB.one (𝟙 _)).1 = Spec.map (CommRingCat.ofHom χB) ≫ originChartι V.toProjective := hχB
  obtain ⟨a, ha, hax, haz⟩ := exists_originChartι_comp_projMap V.toProjective β φ hφ hcoef
  have hsq := (WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom V.toProjective β φ hφ hcoef).w

  have hsemi := comp_eq_comp_of_square (originChartι V.toProjective) (originChartι (V.map β).toProjective)
    (Proj.map φ hφ) (projModelStrCR V.toProjective) (projModelStrCR (V.map β).toProjective) β hsq a ha
    _ (originChartι_comp_projModelStrCR V.toProjective) _ (originChartι_comp_projModelStrCR (V.map β).toProjective)
  have hret := comp_scalar_eq_id (V.map β).toProjective S.1 S.2 χ hχ'
  have hretB := comp_scalar_eq_id V.toProjective (GB.one (𝟙 _)).1 (GB.one (𝟙 _)).2 χB hχB'

  have hker : ∀ z : DualNumber k, z ∈ maximalIdeal (DualNumber k) → (TrivSqZeroExt.fstHom k k k).toRingHom z = 0 := by
    intro z hz
    have h := (IsLocalRing.mem_maximalIdeal _).mp hz
    rw [mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not] at h
    exact h
  have hx0 : (TrivSqZeroExt.fstHom k k k).toRingHom (χ (xOverY (V.map β).toProjective)) = 0 := by
    have : -(χ (xOverY (V.map β).toProjective)) ∈ maximalIdeal (DualNumber k) := hx
    exact hker _ (by simpa using (maximalIdeal (DualNumber k)).neg_mem this)
  have hz0 : (TrivSqZeroExt.fstHom k k k).toRingHom (χ (zOverY (V.map β).toProjective)) = 0 := by
    have : -(χ (zOverY (V.map β).toProjective)) ∈ maximalIdeal (DualNumber k) := hz
    exact hker _ (by simpa using (maximalIdeal (DualNumber k)).neg_mem this)

  have heq : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp χ).comp a =
      ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β).comp χB := by
    refine WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext V _ _ (fun t => ?_) ?_ ?_
    · have e1 := RingHom.congr_fun hsemi t
      have e2 := RingHom.congr_fun hret (β t)
      have e3 := RingHom.congr_fun hretB t
      simp only [RingHom.comp_apply, RingHom.id_apply] at e1 e2 e3 ⊢
      rw [e1, e2, e3]
    · show (TrivSqZeroExt.fstHom k k k).toRingHom (χ (a (xOverY V.toProjective))) =
        (TrivSqZeroExt.fstHom k k k).toRingHom (β (χB (xOverY V.toProjective)))
      rw [hax, hx0, hχBx, map_zero, map_zero]
    · show (TrivSqZeroExt.fstHom k k k).toRingHom (χ (a (zOverY V.toProjective))) =
        (TrivSqZeroExt.fstHom k k k).toRingHom (β (χB (zOverY V.toProjective)))
      rw [haz, hz0, hχBz, map_zero, map_zero]

  have hone := GB.one_natural (𝟙 _) (Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)))
    (Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β))) (Category.comp_id _)
  rw [← hone, schemeHomOverComp_coe, hχB', hχ', Category.assoc, ha, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, heq,
    CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]

end LemmaR

namespace ConstSecAsm
section SectionHalf2

end SectionHalf2

end ConstSecAsm

set_option maxHeartbeats 1600000 in
open ConstSecAsm in
theorem solution
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (B : Type) [CommRing B] [Algebra A B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ)
    (k : Type) [Field k] [CharP k q] (β : B →+* DualNumber k)
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom β)) (projModelStrCR V))
    (hQq : (𝒢 B V hΔ).nsmul _ q Q = (𝒢 B V hΔ).one _)
    (hQ0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 ≠
      ((𝒢 B V hΔ).one (Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)))).1)
    [Algebra A (DualNumber k)] [CharP (DualNumber k) q]
    (hΔW : IsUnit (V.map β).Δ) (hΔq : IsUnit ((V.map β).map (frobenius (DualNumber k) q)).Δ)
    (Φ : projModelCR (V.map β).toProjective ⟶ projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective = projModelStrCR (V.map β).toProjective)
    (hZ : ∃ ψ : ZChartRing ((V.map β).map (frobenius (DualNumber k) q)).toProjective →+* ZChartRing (V.map β).toProjective,
        ψ (xOverZ ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = xOverZ (V.map β).toProjective ^ q ∧
        ψ (yOverZ ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = yOverZ (V.map β).toProjective ^ q ∧
        zChartι (V.map β).toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hΦhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR (V.map β).toProjective)),
      (⟨((𝒢 (DualNumber k) (V.map β) hΔW).mul t x y).1 ≫ Φ, by rw [Category.assoc, hΦ]; exact ((𝒢 (DualNumber k) (V.map β) hΔW).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)) =
        (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t ⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ ⟨y.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact y.2⟩)

    (Vq : projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective ⟶ projModelCR (V.map β).toProjective)
    (hV : Vq ≫ projModelStrCR (V.map β).toProjective = projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hVq : Φ ≫ Vq = (𝒢 (DualNumber k) (V.map β) hΔW).schemeNsmul q)

    (W₃ : WeierstrassCurve (DualNumber k)) (hΔ₃ : IsUnit W₃.Δ)
    (g : projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective ⟶ projModelCR W₃.toProjective)
    (hg : g ≫ projModelStrCR W₃.toProjective = projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hghom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)),
      (⟨((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) =
        (𝒢 (DualNumber k) W₃ hΔ₃).mul t ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩)
    (hK : ∀ (P : Section ((V.map β).map (frobenius (DualNumber k) q)).toProjective) (x₀ y₀ : k),
      IsSectionThrough P (algebraMap k (DualNumber k) x₀) (algebraMap k (DualNumber k) y₀) →
      P.1 ≫ Vq = (kwZeroSect (DualNumber k) (V.map β)).1 →
      P.1 ≫ g = (kwZeroSect (DualNumber k) W₃).1) :
    ∃ (K : Scheme) (ι : K ⟶ projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective),
      IsClosedImmersion ι ∧
      Flat (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ∧
      LocallyOfFinitePresentation (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ∧
      (∀ s, (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective).finrank s = q) ∧
      ι ≫ Vq = (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ≫
        ((𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _)).1 ∧
      ι ≫ g = (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ≫
        ((𝒢 (DualNumber k) W₃ hΔ₃).one (𝟙 _)).1 := by
  classical

  haveI : V.toProjective.toAffine.IsElliptic := ⟨hΔ⟩
  have hGB1' := h𝒢O B V.toProjective hΔ
  have hG1' := h𝒢O (DualNumber k) (V.map β).toProjective hΔW
  have hG1 : ((𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _)).1 = (kwZeroSect (DualNumber k) (V.map β)).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect (V.map β) _).mp hG1'
  have hG31 : ((𝒢 (DualNumber k) W₃ hΔ₃).one (𝟙 _)).1 = (kwZeroSect (DualNumber k) W₃).1 :=
    (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W₃ _).mp
      (h𝒢O (DualNumber k) W₃.toProjective hΔ₃)

  obtain ⟨φβ, hφβ, hcβ⟩ := WeierstrassProjModel.exists_isCoefficientHom V.toProjective β
  have hpb := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom V.toProjective β φβ hφβ hcβ
  obtain ⟨χB, hχB, hχBx, hχBz⟩ := hGB1'
  obtain ⟨χW, hχW, hχWx, hχWz⟩ := hG1'
  have h1 := WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection V.toProjective β φβ hφβ hcβ
    (𝒢 B V hΔ) (𝒢 (DualNumber k) (V.map β) hΔW) χB hχB hχBx hχBz χW hχW hχWx hχWz
  have hK5 := WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq V.toProjective β
    φβ hφβ hcβ (𝒢 B V hΔ) (𝒢 (DualNumber k) (V.map β) hΔW) h1 hpb.w (𝟙 _)

  let QW : Section (V.map β).toProjective :=
    ⟨hpb.lift Q.1 (𝟙 _) (by rw [Category.id_comp]; exact Q.2), hpb.lift_snd _ _ _⟩
  have hQW1 : QW.1 ≫ Proj.map φβ hφβ = Q.1 := hpb.lift_fst _ _ _

  let Q' : SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom β)) (projModelStrCR V.toProjective) :=
    schemeHomOverComp (𝟙 _) rfl Q
  have hQq' : (𝒢 B V hΔ).nsmul _ q Q' = (𝒢 B V hΔ).one _ := by
    show (𝒢 B V hΔ).nsmul _ q (schemeHomOverComp (𝟙 _) rfl Q) = _
    rw [← (𝒢 B V hΔ).nsmul_natural _ _ (𝟙 _) rfl, hQq, (𝒢 B V hΔ).one_natural]
  have hQ'eq : (⟨QW.1 ≫ Proj.map φβ hφβ, by rw [Category.assoc, hpb.w, ← Category.assoc, QW.2]⟩ :
      SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom β)) (projModelStrCR V.toProjective)) = Q' := by
    apply Subtype.ext
    show QW.1 ≫ Proj.map φβ hφβ = 𝟙 _ ≫ Q.1
    rw [hQW1, Category.id_comp]

  have hnsm : ∀ n : ℕ, ((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) n QW).1 ≫ Proj.map φβ hφβ =
      ((𝒢 B V hΔ).nsmul (𝟙 _ ≫ Spec.map (CommRingCat.ofHom β)) n Q').1 := by
    intro n
    induction n with
    | zero =>
      show ((𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _)).1 ≫ Proj.map φβ hφβ = ((𝒢 B V hΔ).one _).1
      rw [h1, ← (𝒢 B V hΔ).one_natural (𝟙 _) _ (𝟙 _ ≫ Spec.map (CommRingCat.ofHom β)) (Category.comp_id _),
        schemeHomOverComp_coe, Category.id_comp]
    | succ n ih =>
      rw [(𝒢 (DualNumber k) (V.map β) hΔW).nsmul_succ, (𝒢 B V hΔ).nsmul_succ, hK5]
      have e1 : (⟨((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) n QW).1 ≫ Proj.map φβ hφβ,
          by rw [Category.assoc, hpb.w, ← Category.assoc, ((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) n QW).2]⟩ :
          SchemeHomOver (𝟙 _ ≫ Spec.map (CommRingCat.ofHom β)) (projModelStrCR V.toProjective)) =
          (𝒢 B V hΔ).nsmul _ n Q' := Subtype.ext ih
      rw [e1, hQ'eq]
  have hQWq : (𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) q QW = (𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _) := by
    apply Subtype.ext
    apply hpb.hom_ext
    · rw [hnsm q, hQq', h1, ← (𝒢 B V hΔ).one_natural (𝟙 _) _ (𝟙 _ ≫ Spec.map (CommRingCat.ofHom β)) (Category.comp_id _),
        schemeHomOverComp_coe, Category.id_comp]
    · rw [((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) q QW).2, ((𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _)).2]

  have hQWaff : ∃ x y : (DualNumber k), IsSectionThrough QW x y := by
    rcases WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_or_exists_reducesToOrigin (V.map β).toProjective QW with h | ⟨χ, hχ⟩
    · exact h
    · exfalso
      apply hQ0
      rw [← hQW1, ← Category.assoc]
      rw [Category.assoc]
      exact specMap_fstHom_comp_projMap_eq_one_of_reducesToOrigin V k β φβ hφβ hcβ (𝒢 B V hΔ) (𝒢 (DualNumber k) (V.map β) hΔW)
        ⟨χB, hχB, hχBx, hχBz⟩ ⟨χW, hχW, hχWx, hχWz⟩ QW χ hχ
  obtain ⟨x, y, ρ, hρ, hρx, hρy⟩ := hQWaff

  let P : Section ((V.map β).map (frobenius (DualNumber k) q)).toProjective := ⟨QW.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact QW.2⟩
  obtain ⟨ψ, hψx, hψy, hψ⟩ := hZ
  have hPthrough : IsSectionThrough P (algebraMap k (DualNumber k) (x.fst ^ q)) (algebraMap k (DualNumber k) (y.fst ^ q)) := by
    refine ⟨ρ.comp ψ, ?_, ?_, ?_⟩
    · show QW.1 ≫ Φ = Spec.map (CommRingCat.ofHom (ρ.comp ψ)) ≫ zChartι ((V.map β).map (frobenius (DualNumber k) q)).toProjective
      rw [show QW.1 = _ from hρ, Category.assoc, hψ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    · show (ρ.comp ψ) (xOverZ _) = _
      rw [RingHom.comp_apply, hψx, map_pow, ← pow_char_eq_algebraMap q x]
      exact congrArg (· ^ q) hρx
    · show (ρ.comp ψ) (yOverZ _) = _
      rw [RingHom.comp_apply, hψy, map_pow, ← pow_char_eq_algebraMap q y]
      exact congrArg (· ^ q) hρy
  have hP0 : ∀ χ : OriginChartRing ((V.map β).map (frobenius (DualNumber k) q)).toProjective →+* (DualNumber k),
      ¬ ReducesToOrigin P χ (IsLocalRing.maximalIdeal (DualNumber k)) :=
    fun χ => not_reducesToOrigin_of_isSectionThrough ((V.map β).map (frobenius (DualNumber k) q)).toProjective P hPthrough χ

  have hK1 := nsmul_comp_eq_of_hom (𝒢 (DualNumber k) (V.map β) hΔW) (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq) Φ hΦ hΦhom (𝟙 _) QW
  have hPq : (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).nsmul (𝟙 _) q P = (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).one (𝟙 _) := by
    have b := congrArg Subtype.val (hK1 0)
    rw [(𝒢 (DualNumber k) (V.map β) hΔW).nsmul_zero, (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).nsmul_zero] at b
    have a : ((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).nsmul (𝟙 _) q P).1 = ((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) q QW).1 ≫ Φ :=
      (congrArg Subtype.val (hK1 q)).symm
    apply Subtype.ext
    rw [a, hQWq]
    exact b

  obtain ⟨K, ι, hci, -, hflat, hlfp, hrk, -, hagree, -⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_isClosedImmersion_finrank_eq_of_nsmul_eq_one_of_not_reducesToOrigin
      A 𝒢 h𝒢 h𝒢O q (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq P hPq hP0

  letI grp := (𝒢 (DualNumber k) (V.map β) hΔW).pointGroup (𝟙 (Spec (CommRingCat.of (DualNumber k))))
  have hpow : ∀ (n : ℕ) (z : Section (V.map β).toProjective), (𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) n z = z ^ n := by
    intro n z
    induction n with
    | zero => rfl
    | succ n ih => rw [(𝒢 (DualNumber k) (V.map β) hΔW).nsmul_succ, pow_succ, ih]; rfl
  have hPV : ∀ i : ℕ, ((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).nsmul (𝟙 _) i P).1 ≫ Vq = ((𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _)).1 := by
    intro i
    have e1 : (((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) i QW).1 ≫ Φ) ≫ Vq =
        ((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) i QW).1 ≫ (𝒢 (DualNumber k) (V.map β) hΔW).schemeNsmul q := by
      rw [Category.assoc, hVq]
    have e2 := comp_schemeNsmul_eq (𝒢 (DualNumber k) (V.map β) hΔW) (𝟙 _) ((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) i QW) q
    have e3 : (𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) q ((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) i QW) =
        (𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _) := by
      rw [hpow i QW, hpow q, ← pow_mul, mul_comm, pow_mul, ← hpow q QW, hQWq, ← hpow i,
        RelativeGroupLaw.nsmul_unit]
    have a : ((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).nsmul (𝟙 _) i P).1 = ((𝒢 (DualNumber k) (V.map β) hΔW).nsmul (𝟙 _) i QW).1 ≫ Φ :=
      (congrArg Subtype.val (hK1 i)).symm
    rw [a, e1, e2, e3]
  have hιV : ι ≫ Vq = (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ≫ ((𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _)).1 :=
    comp_eq_comp_one_of_forall_nsmul (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq) (𝒢 (DualNumber k) (V.map β) hΔW) P ι hagree Vq hPV

  have hPV1 : P.1 ≫ Vq = (kwZeroSect (DualNumber k) (V.map β)).1 := by
    have := hPV 1
    rwa [(𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).nsmul_one_apply, hG1] at this
  have hPg : (⟨P.1 ≫ g, by rw [Category.assoc, hg]; exact P.2⟩ : Section W₃.toProjective) = (𝒢 (DualNumber k) W₃ hΔ₃).one (𝟙 _) := by
    apply Subtype.ext
    show P.1 ≫ g = _
    rw [hG31]
    exact hK P _ _ hPthrough hPV1
  have hιg : ι ≫ g = (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ≫ ((𝒢 (DualNumber k) W₃ hΔ₃).one (𝟙 _)).1 :=
    comp_eq_comp_one_of_hom_of_comp_eq_one (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq) (𝒢 (DualNumber k) W₃ hΔ₃) P ι hagree g hg hghom hPg
  exact ⟨K, ι, hci, hflat, hlfp, hrk, hιV, hιg⟩

end S_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one (solution)
