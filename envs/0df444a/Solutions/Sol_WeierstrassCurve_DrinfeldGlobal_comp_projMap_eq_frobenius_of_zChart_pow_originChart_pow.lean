-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1a7eaf27-359d-57c7-9ec2-3d7182e35747

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PsiIsFrobeniusAux

open HomogeneousLocalization MvPolynomial HomogeneousIdealQuotientGrading

section Cover

variable {T : Type} [CommRing T]

theorem exists_coord_zero_pow_three_eq (W : WeierstrassCurve.Projective T) :
    ∃ r : ProjModelRingCR W, coord W 0 ^ 3 = coord W 2 * r := by
  refine ⟨Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal
    (X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 * X 2
      - C W.a₂ * X 0 ^ 2 - C W.a₄ * X 0 * X 2 - C W.a₆ * X 2 ^ 2), ?_⟩
  have hP : Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal W.polynomial = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, projModelHomogeneousIdealCR_toIdeal]
    exact Ideal.mem_span_singleton_self _
  have hid : (X 0 : MvPolynomial (Fin 3) T) ^ 3 =
      X 2 * (X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 * X 2
        - C W.a₂ * X 0 ^ 2 - C W.a₄ * X 0 * X 2 - C W.a₆ * X 2 ^ 2) - W.polynomial := by
    rw [WeierstrassCurve.Projective.polynomial]; ring
  show Ideal.Quotient.mk _ (X 0) ^ 3 = Ideal.Quotient.mk _ (X 2) * Ideal.Quotient.mk _ _
  rw [← map_pow, hid, map_sub, hP, sub_zero, map_mul]

theorem mem_basicOpen_one_of_not_mem (W : WeierstrassCurve.Projective T) (x : projModelCR W)
    (hZ : x ∉ Proj.basicOpen (projModelGradingCR W) (coord W 2)) :
    x ∈ Proj.basicOpen (projModelGradingCR W) (coord W 1) := by
  have hZmem : coord W 2 ∈ x.asHomogeneousIdeal := by
    rwa [Proj.mem_basicOpen, not_not] at hZ
  have hXmem : coord W 0 ∈ x.asHomogeneousIdeal := by
    obtain ⟨r, hr⟩ := exists_coord_zero_pow_three_eq W
    have h3 : coord W 0 ^ 3 ∈ x.asHomogeneousIdeal := by
      rw [hr]; exact Ideal.mul_mem_right _ _ hZmem
    exact x.isPrime.mem_of_pow_mem 3 h3
  rw [Proj.mem_basicOpen]
  intro hY
  apply x.not_irrelevant_le
  refine (WeierstrassProjModel.kw_pbac_irrelevant_le_span_mk_X_CR T W).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hXmem
  · exact hY
  · exact hZmem

theorem hom_ext_of_charts (W : WeierstrassCurve.Projective T) {Y : Scheme} (f g : projModelCR W ⟶ Y)
    (h₁ : originChartι W ≫ f = originChartι W ≫ g) (h₂ : zChartι W ≫ f = zChartι W ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall f g fun x => ?_
  by_cases hx : x ∈ Proj.basicOpen (projModelGradingCR W) (coord W 2)
  · refine ⟨(zChartι W).opensRange, ?_, ?_⟩
    · show x ∈ (Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos).opensRange
      rw [Proj.opensRange_awayι]; exact hx
    · rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, h₂]
  · refine ⟨(originChartι W).opensRange, ?_, ?_⟩
    · show x ∈ (Proj.awayι (projModelGradingCR W) (coord W 1) (coord_mem W 1) one_pos).opensRange
      rw [Proj.opensRange_awayι]; exact mem_basicOpen_one_of_not_mem W x hx
    · rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc, h₁]

theorem zChartι_comp_projModelStrCR (W : WeierstrassCurve.Projective T) :
    zChartι W ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom ((fromZeroRingHom (projModelGradingCR W) _).comp
        (algebraMap T ((projModelGradingCR W) 0)))) := by
  show Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos ≫ projModelStrCR W = _
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem originChartι_comp_projModelStrCR (W : WeierstrassCurve.Projective T) :
    originChartι W ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom ((fromZeroRingHom (projModelGradingCR W) _).comp
        (algebraMap T ((projModelGradingCR W) 0)))) := by
  show Proj.awayι (projModelGradingCR W) (coord W 1) (coord_mem W 1) one_pos ≫ projModelStrCR W = _
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end Cover

section Scalars

theorem comp_eq_of_comp_eq_specMap_comp {X Y : Scheme} {R R' : Type} [CommRing R] [CommRing R']
    {T : Type} [CommRing T]
    (c : Spec (CommRingCat.of R) ⟶ X) (c' : Spec (CommRingCat.of R') ⟶ Y) (Φ : X ⟶ Y)
    (pX : X ⟶ Spec (CommRingCat.of T)) (pY : Y ⟶ Spec (CommRingCat.of T)) (hΦ : Φ ≫ pY = pX)
    (s : T →+* R) (hs : c ≫ pX = Spec.map (CommRingCat.ofHom s))
    (s' : T →+* R') (hs' : c' ≫ pY = Spec.map (CommRingCat.ofHom s'))
    (ψ : R' →+* R) (hψ : c ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ c') :
    ψ.comp s' = s := by
  have e : Spec.map (CommRingCat.ofHom (ψ.comp s')) = Spec.map (CommRingCat.ofHom s) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← hs', ← Category.assoc, ← hψ, Category.assoc, hΦ, hs]
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

end Scalars

section ChartGen

variable {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T)

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
    Away.mk (projModelGradingCR W) (coord_mem W 2) a x hx = xOverZ W ^ ai 0 * yOverZ W ^ ai 1 := by
  apply val_injective
  simp only [val_mul, val_pow, xOverZ, yOverZ, Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, hxeq, Fin.prod_univ_three]
  rw [← hai]
  ring

theorem ringHom_zChartRing_ext {B : Type} [CommRing B]
    (χ χ' : ZChartRing W →+* B)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      χ' (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)))
    (hx : χ (xOverZ W) = χ' (xOverZ W)) (hy : χ (yOverZ W) = χ' (yOverZ W)) :
    χ = χ' := by
  classical
  have hZ : coord W 2 ∈ projModelGradingCR W 1 := coord_mem W 2
  apply RingHom.ext
  intro z
  have hzs : z ∈ Submodule.span ((projModelGradingCR W) 0)
      { (Away.mk (projModelGradingCR W) hZ a (∏ i, coord W i ^ ai i)
          (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ coord_mem W i) : Away (projModelGradingCR W) (coord W 2)) |
        (a : ℕ) (ai : Fin 3 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) } := by
    rw [Away.span_mk_prod_pow_eq_top hZ (coord W) (adjoin_range_coord_eq_top W) (fun _ => 1) (fun i => coord_mem W i)]
    trivial
  induction hzs using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ai, hai, rfl⟩ := hz
      have hai' : ai 0 + ai 1 + ai 2 = a := by simpa [Fin.sum_univ_three] using hai
      rw [mk_prod_pow_eq W a ai hai' _ rfl, map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, hx, hy]
  | zero => simp
  | add x y _ _ hx' hy' => rw [map_add, map_add, hx', hy']
  | smul r x _ hx' =>
      obtain ⟨t, ht⟩ := exists_coe_eq_cls_C W r
      have hr : r = algebraMap T ((projModelGradingCR W) 0) t := Subtype.ext (by rw [ht, coe_algebraMap_zero])
      rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_eq, map_mul, map_mul, hx', hr, hsc t]

end ChartGen

end PsiIsFrobeniusAux

open PsiIsFrobeniusAux HomogeneousLocalization

theorem solution
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [CharP T q]
    (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map (frobenius T q)).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (frobenius T q)).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective (frobenius T q) φ)
    (hE : (q : Γ(projModelCR W.toProjective, ⊤)) = 0) :
    Φ ≫ Proj.map φ hφ = (projModelCR W.toProjective).frobenius q 1 Fact.out hE := by
  classical
  obtain ⟨ψ, hψx, hψy, hψ⟩ := hZ
  obtain ⟨χ₁, hχ₁x, hχ₁z, hχ₁⟩ := hY
  have hq : (q : T) = 0 := CharP.cast_eq_zero T q
  have hsq := (WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W.toProjective
    (frobenius T q) φ hφ hcoef).w
  apply hom_ext_of_charts W.toProjective
  ·
    obtain ⟨χ, hχ, hχs, hχx, hχz⟩ :=
      WeierstrassCurve.DrinfeldGlobal.exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom W.toProjective
        (frobenius T q) φ hφ hcoef χ₁
    have hR : (q : OriginChartRing W.toProjective) = 0 := by
      rw [← map_natCast ((fromZeroRingHom (projModelGradingCR W.toProjective) _).comp
        (algebraMap T ((projModelGradingCR W.toProjective) 0))) q, hq, map_zero]

    have hlin := comp_eq_of_comp_eq_specMap_comp (originChartι W.toProjective)
      (originChartι (W.map (frobenius T q)).toProjective) Φ (projModelStrCR W.toProjective)
      (projModelStrCR (W.map (frobenius T q)).toProjective) hΦ _ (originChartι_comp_projModelStrCR W.toProjective)
      _ (originChartι_comp_projModelStrCR (W.map (frobenius T q)).toProjective) χ₁ hχ₁
    have hlin' : ∀ u : T, χ₁ ((fromZeroRingHom (projModelGradingCR (W.map (frobenius T q)).toProjective) _)
        (algebraMap T ((projModelGradingCR (W.map (frobenius T q)).toProjective) 0) u)) =
        (fromZeroRingHom (projModelGradingCR W.toProjective) _) (algebraMap T ((projModelGradingCR W.toProjective) 0) u) :=
      fun u => by simpa only [RingHom.comp_apply] using RingHom.congr_fun hlin u
    have hχeq : χ = powCharRingHom (OriginChartRing W.toProjective) q 1 Fact.out hR := by
      refine WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W χ _ (fun t => ?_) ?_ ?_
      · rw [hχs t, hlin' (frobenius T q t)]
        simp only [frobenius_def, map_pow, powCharRingHom_apply, pow_one]
      · rw [hχx, hχ₁x, powCharRingHom_apply, pow_one]
      · rw [hχz, hχ₁z, powCharRingHom_apply, pow_one]
    rw [← Category.assoc, hχ₁, Category.assoc, hχ, hχeq,
      ← Scheme.frobenius_comp (originChartι W.toProjective) q 1 Fact.out (Scheme.natCast_eq_zero_ΓSpec hR) hE,
      Scheme.frobenius_Spec q 1 Fact.out hR]
  ·
    obtain ⟨a, ha, hax, hay⟩ :=
      WeierstrassCurve.DrinfeldGlobal.exists_zChartIota_comp_projMap_eq_specMap_comp_zChartIota W.toProjective
        (frobenius T q) φ hφ hcoef
    have hR : (q : ZChartRing W.toProjective) = 0 := by
      rw [← map_natCast ((fromZeroRingHom (projModelGradingCR W.toProjective) _).comp
        (algebraMap T ((projModelGradingCR W.toProjective) 0))) q, hq, map_zero]
    have hlin := comp_eq_of_comp_eq_specMap_comp (zChartι W.toProjective)
      (zChartι (W.map (frobenius T q)).toProjective) Φ (projModelStrCR W.toProjective)
      (projModelStrCR (W.map (frobenius T q)).toProjective) hΦ _ (zChartι_comp_projModelStrCR W.toProjective)
      _ (zChartι_comp_projModelStrCR (W.map (frobenius T q)).toProjective) ψ hψ
    have hsemi := comp_eq_comp_of_square (zChartι W.toProjective) (zChartι (W.map (frobenius T q)).toProjective)
      (Proj.map φ hφ) (projModelStrCR W.toProjective) (projModelStrCR (W.map (frobenius T q)).toProjective)
      (frobenius T q) hsq a ha _ (zChartι_comp_projModelStrCR W.toProjective)
      _ (zChartι_comp_projModelStrCR (W.map (frobenius T q)).toProjective)
    have hlin' : ∀ u : T, ψ ((fromZeroRingHom (projModelGradingCR (W.map (frobenius T q)).toProjective) _)
        (algebraMap T ((projModelGradingCR (W.map (frobenius T q)).toProjective) 0) u)) =
        (fromZeroRingHom (projModelGradingCR W.toProjective) _) (algebraMap T ((projModelGradingCR W.toProjective) 0) u) :=
      fun u => by simpa only [RingHom.comp_apply] using RingHom.congr_fun hlin u
    have hsemi' : ∀ u : T, a ((fromZeroRingHom (projModelGradingCR W.toProjective) _)
        (algebraMap T ((projModelGradingCR W.toProjective) 0) u)) =
        (fromZeroRingHom (projModelGradingCR (W.map (frobenius T q)).toProjective) _)
          (algebraMap T ((projModelGradingCR (W.map (frobenius T q)).toProjective) 0) (frobenius T q u)) :=
      fun u => by simpa only [RingHom.comp_apply] using RingHom.congr_fun hsemi u
    have heq : ψ.comp a = powCharRingHom (ZChartRing W.toProjective) q 1 Fact.out hR := by
      refine ringHom_zChartRing_ext W.toProjective _ _ (fun t => ?_) ?_ ?_
      · rw [RingHom.comp_apply, hsemi' t, hlin' (frobenius T q t)]
        simp only [frobenius_def, map_pow, powCharRingHom_apply, pow_one]
      · rw [RingHom.comp_apply, hax, hψx, powCharRingHom_apply, pow_one]
      · rw [RingHom.comp_apply, hay, hψy, powCharRingHom_apply, pow_one]
    rw [← Category.assoc, hψ, Category.assoc, ha, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, heq,
      ← Scheme.frobenius_comp (zChartι W.toProjective) q 1 Fact.out (Scheme.natCast_eq_zero_ΓSpec hR) hE,
      Scheme.frobenius_Spec q 1 Fact.out hR]

end S_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow (solution)
