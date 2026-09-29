-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comp_projMap_eq_at_field_of_isCoefficientHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bd5abf5a-24f5-5d9c-b653-8d4fd673f443

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_of_isPullback
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comp_projMap_eq_at_field_of_isCoefficientHom
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

namespace CFieldAux

open HomogeneousLocalization MvPolynomial HomogeneousIdealQuotientGrading

section AwayCongr

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

def awayCongr {s s' : A} (e : s = s') : Away 𝒜 s ≃+* Away 𝒜 s' := by
  subst e; exact RingEquiv.refl _

lemma awayCongr_mk {s s' : A} (e : s = s') {d : ℕ} (hs : s ∈ 𝒜 d) (hs' : s' ∈ 𝒜 d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    awayCongr 𝒜 e (Away.mk 𝒜 hs n x hx) = Away.mk 𝒜 hs' n x hx := by
  subst e; rfl

lemma awayι_eq_specMap_awayCongr_comp {s s' : A} (e : s = s') {i : ℕ} (hs : s ∈ 𝒜 i) (hs' : s' ∈ 𝒜 i)
    (hi : 0 < i) :
    Proj.awayι 𝒜 s' hs' hi =
      Spec.map (CommRingCat.ofHom (awayCongr 𝒜 e).toRingHom) ≫ Proj.awayι 𝒜 s hs hi := by
  subst e
  have : (awayCongr 𝒜 (rfl : s = s)).toRingHom = RingHom.id _ := rfl
  rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

lemma fromZeroRingHom_eq_mk {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (r : 𝒜 0) :
    fromZeroRingHom 𝒜 (Submonoid.powers s) r = Away.mk 𝒜 hs 0 (r : A) (by simpa using r.2) := by
  apply val_injective
  rw [Away.val_mk]
  show Localization.mk (r : A) _ = Localization.mk (r : A) _
  congr 1
  exact Subtype.ext (pow_zero s).symm

end AwayCongr

section Model

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

lemma coe_algebraMap_zero (t : T) :
    ((algebraMap T ((projModelGradingCR W) 0) t : (projModelGradingCR W) 0) : ProjModelRingCR W) = cls W (C t) := by
  rw [SetLike.GradeZero.coe_algebraMap]; rfl

lemma exists_coe_eq_cls_C (r : (projModelGradingCR W) 0) : ∃ t : T, (r : ProjModelRingCR W) = cls W (C t) := by
  obtain ⟨p, hp, hpr⟩ := (mem_quotGradingSubmodule_iff _ _).mp r.2
  have hp0 : p.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 p).mp hp
  refine ⟨p.coeff 0, ?_⟩
  rw [← hpr]
  by_cases h0 : p = 0
  · subst h0; simp [cls]
  · have htd : p.totalDegree = 0 := hp0.totalDegree h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at htd
    exact congrArg _ htd

lemma adjoin_range_coord_eq_top :
    Algebra.adjoin ((projModelGradingCR W) 0) (Set.range (coord W)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C t =>
      have : (Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (C t) : ProjModelRingCR W) =
          algebraMap ((projModelGradingCR W) 0) (ProjModelRingCR W) (algebraMap T ((projModelGradingCR W) 0) t) := by
        rw [SetLike.GradeZero.algebraMap_apply, coe_algebraMap_zero]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

lemma mk_prod_pow_eq (a : ℕ) (ai : Fin 3 → ℕ) (hai : ai 0 + ai 1 + ai 2 = a)
    (x : ProjModelRingCR W) (hxeq : x = ∏ i, coord W i ^ ai i) (hx : x ∈ projModelGradingCR W (a • 1)) :
    Away.mk (projModelGradingCR W) (coord_mem W 1) a x hx = xOverY W ^ ai 0 * zOverY W ^ ai 2 := by
  apply val_injective
  simp only [val_mul, val_pow, xOverY, zOverY, Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, hxeq, Fin.prod_univ_three]
  rw [← hai]
  ring

lemma apply_sc_eq {G : RelativeGroupLaw T (projModelStrCR W)} (χ : OriginChartRing W →+* T)
    (hχ : IsOriginChartSection (G.one (𝟙 _)) χ) (t : T) :
    χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
  have h := (G.one (𝟙 (Spec (CommRingCat.of T)))).2
  rw [hχ] at h
  simp only [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0)) ≫
      CommRingCat.ofHom (fromZeroRingHom (projModelGradingCR W) _) ≫ CommRingCat.ofHom χ) =
      Spec.map (𝟙 _) := by rw [Spec.map_id]; exact h
  have h3 := Spec.map_injective h2
  have h4 := congrArg (fun g : CommRingCat.of T ⟶ CommRingCat.of T => g.hom t) h3
  simpa using h4

end Model

section Ext

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

theorem originChart_ringHom_ext {S : Type u} [CommRing S] (g₁ g₂ : OriginChartRing W →+* S)
    (hsc : ∀ t : T, g₁ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      g₂ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)))
    (hx : g₁ (xOverY W) = g₂ (xOverY W)) (hz : g₁ (zOverY W) = g₂ (zOverY W)) : g₁ = g₂ := by
  classical
  have hY : coord W 1 ∈ projModelGradingCR W 1 := coord_mem W 1
  apply RingHom.ext
  intro z
  have hz' : z ∈ Submodule.span ((projModelGradingCR W) 0)
      { (Away.mk (projModelGradingCR W) hY a (∏ i, coord W i ^ ai i)
          (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ coord_mem W i) : Away (projModelGradingCR W) (coord W 1)) |
        (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) } := by
    rw [Away.span_mk_prod_pow_eq_top hY (coord W) (adjoin_range_coord_eq_top W) (fun _ => 1) (fun i => coord_mem W i)]
    trivial
  induction hz' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ai, hai, rfl⟩ := hz
      have hai' : ai 0 + ai 1 + ai 2 = a := by simpa [Fin.sum_univ_three] using hai
      rw [mk_prod_pow_eq W a ai hai' _ rfl, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, hx, hz]
  | zero => simp
  | add x y _ _ hx' hy' => rw [map_add, map_add, hx', hy']
  | smul r x _ hx' =>
      obtain ⟨t, ht⟩ := exists_coe_eq_cls_C W r
      have hr : r = algebraMap T ((projModelGradingCR W) 0) t := Subtype.ext (by rw [ht, coe_algebraMap_zero])
      rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_eq, map_mul, map_mul, hx', hr, hsc t]

theorem kwYChartEval_mk_coord (V : WeierstrassCurve T) (i : Fin 3)
    (hi : coord V.toProjective i ∈ projModelGradingCR V.toProjective (1 • 1)) :
    kwYChartEval T V (Away.mk (projModelGradingCR V.toProjective) (coord_mem V.toProjective 1) 1 (coord V.toProjective i) hi) =
      kwYEvalRingHom T V (coord V.toProjective i) := by
  have hunit : IsUnit (kwYEvalRingHom T V (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) T))) :=
    kwYEvalRingHom_mk_X1 T V ▸ isUnit_one
  have hY1 : kwYEvalRingHom T V (coord V.toProjective 1 ^ 1) = 1 := by
    rw [pow_one]; exact kwYEvalRingHom_mk_X1 T V
  simp only [kwYChartEval, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  have h1 : (Localization.mk (coord V.toProjective i)
      ⟨coord V.toProjective 1 ^ 1, ⟨1, rfl⟩⟩ : Localization.Away (coord V.toProjective 1)) *
      algebraMap _ _ (coord V.toProjective 1 ^ 1) = algebraMap _ _ (coord V.toProjective i) := by
    rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (IsLocalization.Away.lift (coord V.toProjective 1) (g := kwYEvalRingHom T V) hunit) h1
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, hY1, mul_one] at h2
  exact h2

theorem kwYChartEval_xOverY (V : WeierstrassCurve T) :
    kwYChartEval T V (xOverY V.toProjective) = 0 ∧ kwYChartEval T V (zOverY V.toProjective) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [xOverY, kwYChartEval_mk_coord]
    show (MvPolynomial.eval ![(0 : T), 1, 0]) (MvPolynomial.X 0) = 0
    simp
  · rw [zOverY, kwYChartEval_mk_coord]
    show (MvPolynomial.eval ![(0 : T), 1, 0]) (MvPolynomial.X 2) = 0
    simp

theorem eq_kwZeroSect_of_isOriginChartSection (V : WeierstrassCurve T)
    {G : RelativeGroupLaw T (projModelStrCR V.toProjective)} (χ : OriginChartRing V.toProjective →+* T)
    (hχ : IsOriginChartSection (G.one (𝟙 _)) χ) (hχx : χ (xOverY V.toProjective) = 0) (hχz : χ (zOverY V.toProjective) = 0) :
    (G.one (𝟙 _)).1 = (kwZeroSect T V).1 := by
  have hχeq : χ = kwYChartEval T V := by
    apply originChart_ringHom_ext V.toProjective
    · intro t
      rw [apply_sc_eq V.toProjective χ hχ t]
      exact (RingHom.congr_fun (kwYChartEval_section T V) t).symm
    · rw [hχx, (kwYChartEval_xOverY V).1]
    · rw [hχz, (kwYChartEval_xOverY V).2]
  rw [hχ, hχeq]
  rfl

end Ext

end CFieldAux

set_option maxHeartbeats 3200000 in
open CFieldAux in
theorem solution
    (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type u) [CommRing T] [Algebra A T] (K : Type u) [Field K] [Algebra A K] (f : T →ₐ[A] K)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (W.map f.toRingHom).Δ)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hφc : IsCoefficientHom W f.toRingHom φ)
    (F : Type u) [Field F] [Algebra K F]
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR (W.map f.toRingHom)))
    (x' y' : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) (projModelStrCR W))
    (hx : x'.1 = x.1 ≫ Proj.map φ hφ) (hy : y'.1 = y.1 ≫ Proj.map φ hφ) :
    ((𝒢 K (W.map f.toRingHom) hΔ').mul (Spec.map (CommRingCat.ofHom (algebraMap K F))) x y).1 ≫ Proj.map φ hφ =
      ((𝒢 T W hΔ).mul
        (Spec.map (CommRingCat.ofHom (algebraMap K F)) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) x' y').1 := by
  classical
  haveI hE : WeierstrassCurve.IsElliptic (W.map f.toRingHom) := ⟨hΔ'⟩
  have hP := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W f.toRingHom φ hφ hφc

  obtain ⟨G', hmul, hone⟩ := WeierstrassProjModel.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_of_isPullback
    f.toRingHom (projModelStrCR W) (projModelStrCR (W.map f.toRingHom)) (Proj.map φ hφ) hP (𝒢 T W hΔ)

  obtain ⟨χ, hχ, hχx, hχz⟩ := h𝒢O T W hΔ
  obtain ⟨χ', hχ', hχ'x, hχ'z⟩ := h𝒢O K (W.map f.toRingHom) hΔ'
  have hLone : ((𝒢 K (W.map f.toRingHom) hΔ').one (𝟙 _)).1 = (kwZeroSect K (W.map f.toRingHom)).1 :=
    eq_kwZeroSect_of_isOriginChartSection (W.map f.toRingHom) χ' hχ' hχ'x hχ'z
  have hK8 := WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection W f.toRingHom φ hφ hφc
      (𝒢 T W hΔ) (𝒢 K (W.map f.toRingHom) hΔ') χ hχ hχx hχz χ' hχ' hχ'x hχ'z
  have hone₁ : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of K)),
      ((𝒢 K (W.map f.toRingHom) hΔ').one t).1 = t ≫ (kwZeroSect K (W.map f.toRingHom)).1 := by
    intro S t
    rw [← (𝒢 K (W.map f.toRingHom) hΔ').one_natural (𝟙 _) t t (Category.comp_id t), schemeHomOverComp_coe, hLone]
  have hone₀ : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of K)),
      (G'.one t).1 = t ≫ (kwZeroSect K (W.map f.toRingHom)).1 := by
    intro S t
    apply hP.hom_ext
    · rw [hone, Category.assoc, ← hLone, hK8,
        ← (𝒢 T W hΔ).one_natural (𝟙 _) (t ≫ Spec.map (CommRingCat.ofHom f.toRingHom))
          (t ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) (Category.comp_id _), schemeHomOverComp_coe, Category.assoc]
    · rw [(G'.one t).2, Category.assoc, (kwZeroSect K _).2, Category.comp_id]

  have huniq := WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_zeroSect_of_isElliptic_of_baseChangeIso
    (W.map f.toRingHom)
    (WeierstrassProjModel.projModel_pullback_iso_baseChange (W.map f.toRingHom)) G' (𝒢 K (W.map f.toRingHom) hΔ')
    hone₀ hone₁ F x y
  have hx'' : x' = ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩ := Subtype.ext hx
  have hy'' : y' = ⟨y.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩ := Subtype.ext hy
  rw [hx'', hy'', ← huniq, hmul]

end S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comp_projMap_eq_at_field_of_isCoefficientHom
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comp_projMap_eq_at_field_of_isCoefficientHom (solution)
