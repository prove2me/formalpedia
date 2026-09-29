-- Prove2me | solution 1 for V3AsmLevel.exists_smoothOffEdges
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0ba3da31-1890-5257-87d9-408cbff8b0f7

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSiteLevel
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_preimage_smoothLocus_le_of_isPullback
import Theorems.Thm_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isProper_toCrossing
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isIntegral_pullback_toBase_specMap
import Theorems.Thm_ModularCurve_DRLevel_bcMap_apply_notMem_preimage_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3AsmLevel_exists_smoothOffEdges
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

namespace ModelSmooth

variable (R : Type u) [CommRing R]

example : Algebra.FinitePresentation R R[X] := inferInstance
example : Subsingleton (Algebra.H1Cotangent R R[X]) := inferInstance

private noncomputable def kaehlerBasisPolynomial : Module.Basis Unit R[X] (Ω[R[X]⁄R]) :=
  (Module.Basis.singleton Unit R[X]).map (KaehlerDifferential.polynomialEquiv R).symm

private theorem kaehlerBasisPolynomial_apply (i : Unit) : kaehlerBasisPolynomial R i = KaehlerDifferential.D R R[X] X := by
  simp [kaehlerBasisPolynomial, KaehlerDifferential.polynomialEquiv_symm]

private theorem isStandardSmooth_polynomial : Algebra.IsStandardSmooth R R[X] :=
  Algebra.IsStandardSmooth.of_basis_kaehlerDifferential (kaehlerBasisPolynomial R) (by
    rintro _ ⟨i, rfl⟩
    exact ⟨X, (kaehlerBasisPolynomial_apply R i).symm⟩)

private theorem isStandardSmoothOfRelativeDimension_one_polynomial [Nontrivial R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R R[X] := by
  haveI := isStandardSmooth_polynomial R
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [rank_eq_card_basis (kaehlerBasisPolynomial R)]
  simp

private theorem isStandardSmoothOfRelativeDimension_one_of_isLocalization_away_X [Nontrivial R] (S : Type u) [CommRing S]
    [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S] [IsLocalization.Away (X : R[X]) S] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R S := by
  haveI := isStandardSmoothOfRelativeDimension_one_polynomial R
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 R[X] S :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (X : R[X])
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 R R[X] S

end ModelSmooth

namespace MvPolynomial
p2m_export "MvPolynomial" "X map coeff R aeval_X ext support aeval_def algebraMap_apply comap algebraMap_eq C monomial coeff_zero sum_def notMem_support_iff aeval_C induction_on aeval CrossingQuotient.Resolution CrossingQuotient.Resolution.exists_ι_apply_eq CrossingQuotient.Resolution.toCrossing CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.Resolution.isProper_toCrossing"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.exists_ι_apply_eq Resolution.toCrossing Resolution.toSpec U V U_mul_V lift mk mk_surjective monomial monomial_natCast monomial_neg_natCast originIdeal linearIndependent_monomial_and_span_eq_top Resolution.isProper_toCrossing"
p2m_open "MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W)

private noncomputable abbrev polyU : W[X] →ₐ[W] CrossingQuotient W t := Polynomial.aeval (U t)

private noncomputable abbrev polyV : W[X] →ₐ[W] CrossingQuotient W t := Polynomial.aeval (V t)

private theorem polyU_injective : Function.Injective (polyU t) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hli : LinearIndependent W (fun n : ℕ => monomial t (n : ℤ)) :=
    (linearIndependent_monomial_and_span_eq_top t).1.comp _ Nat.cast_injective
  have hsum : polyU t p = ∑ n ∈ p.support, p.coeff n • monomial t (n : ℤ) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [monomial_natCast]
    exact (Algebra.smul_def _ _).symm
  rw [hsum] at hp
  have h0 := linearIndependent_iff'.mp hli p.support (fun n => p.coeff n) hp
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n ∈ p.support
  · exact h0 n hn
  · exact Polynomial.notMem_support_iff.mp hn

private theorem polyV_injective : Function.Injective (polyV t) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hli : LinearIndependent W (fun n : ℕ => monomial t (-(n : ℤ))) :=
    (linearIndependent_monomial_and_span_eq_top t).1.comp (fun n : ℕ => -(n : ℤ))
      (fun a b h => Nat.cast_injective (neg_injective h))
  have hsum : polyV t p = ∑ n ∈ p.support, p.coeff n • monomial t (-(n : ℤ)) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [monomial_neg_natCast]
    exact (Algebra.smul_def _ _).symm
  rw [hsum] at hp
  have h0 := linearIndependent_iff'.mp hli p.support (fun n => p.coeff n) hp
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n ∈ p.support
  · exact h0 n hn
  · exact Polynomial.notMem_support_iff.mp hn

private theorem exists_mul_U_pow_eq_polyU (c : CrossingQuotient W t) : ∃ (n : ℕ) (q : W[X]), c * U t ^ n = polyU t q := by
  obtain ⟨f, rfl⟩ := mk_surjective t c
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, Polynomial.C a, by rw [pow_zero, mul_one, Polynomial.aeval_C]; exact (mk t).commutes a⟩
  | add p q hp hq =>
    obtain ⟨n₁, q₁, h₁⟩ := hp
    obtain ⟨n₂, q₂, h₂⟩ := hq
    refine ⟨n₁ + n₂, q₁ * Polynomial.X ^ n₂ + q₂ * Polynomial.X ^ n₁, ?_⟩
    rw [map_add, add_mul, map_add, map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_X, ← h₁, ← h₂]
    ring
  | mul_X p i hp =>
    obtain ⟨n, q, h⟩ := hp
    fin_cases i
    · refine ⟨n, q * Polynomial.X, ?_⟩
      rw [map_mul, map_mul, Polynomial.aeval_X, ← h]
      show mk t p * U t * U t ^ n = mk t p * U t ^ n * U t
      ring
    · refine ⟨n + 1, Polynomial.C t * q, ?_⟩
      rw [map_mul, map_mul, Polynomial.aeval_C, ← h]
      show mk t p * V t * U t ^ (n + 1) = algebraMap W _ t * (mk t p * U t ^ n)
      rw [pow_succ, ← U_mul_V]
      ring

private theorem exists_mul_V_pow_eq_polyV (c : CrossingQuotient W t) : ∃ (n : ℕ) (q : W[X]), c * V t ^ n = polyV t q := by
  obtain ⟨f, rfl⟩ := mk_surjective t c
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, Polynomial.C a, by rw [pow_zero, mul_one, Polynomial.aeval_C]; exact (mk t).commutes a⟩
  | add p q hp hq =>
    obtain ⟨n₁, q₁, h₁⟩ := hp
    obtain ⟨n₂, q₂, h₂⟩ := hq
    refine ⟨n₁ + n₂, q₁ * Polynomial.X ^ n₂ + q₂ * Polynomial.X ^ n₁, ?_⟩
    rw [map_add, add_mul, map_add, map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_X, ← h₁, ← h₂]
    ring
  | mul_X p i hp =>
    obtain ⟨n, q, h⟩ := hp
    fin_cases i
    · refine ⟨n + 1, Polynomial.C t * q, ?_⟩
      rw [map_mul, map_mul, Polynomial.aeval_C, ← h]
      show mk t p * U t * V t ^ (n + 1) = algebraMap W _ t * (mk t p * V t ^ n)
      rw [pow_succ, ← U_mul_V]
      ring
    · refine ⟨n, q * Polynomial.X, ?_⟩
      rw [map_mul, map_mul, Polynomial.aeval_X, ← h]
      show mk t p * V t * V t ^ n = mk t p * V t ^ n * V t
      ring

section awayU

private theorem isStandardSmoothOfRelativeDimension_one_awayU [Nontrivial W] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 W (Localization.Away (U t)) := by
  letI alg : Algebra W[X] (Localization.Away (U t)) :=
    ((algebraMap (CrossingQuotient W t) (Localization.Away (U t))).comp (polyU t).toRingHom).toAlgebra
  letI smulAlg : SMul W[X] (Localization.Away (U t)) := alg.toSMul
  have halg : ∀ q : W[X], algebraMap W[X] (Localization.Away (U t)) q =
      algebraMap (CrossingQuotient W t) _ (polyU t q) := fun q => rfl
  haveI : IsScalarTower W W[X] (Localization.Away (U t)) :=
    IsScalarTower.of_algebraMap_eq (R := W) (S := W[X]) (A := Localization.Away (U t)) fun w => by
      rw [halg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization.Away (Polynomial.X : W[X]) (Localization.Away (U t)) :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        rw [halg, map_pow, Polynomial.aeval_X, map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit (U t)).pow n
      surj := fun z => by
        obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (U t)) z
        obtain ⟨n, q, hq⟩ := exists_mul_U_pow_eq_polyU t c
        refine ⟨⟨q, ⟨Polynomial.X ^ (m + n), _, rfl⟩⟩, ?_⟩
        show IsLocalization.mk' _ c ⟨U t ^ m, _⟩ * algebraMap W[X] _ (Polynomial.X ^ (m + n)) = algebraMap W[X] _ q
        rw [halg, halg, map_pow, Polynomial.aeval_X, pow_add, map_mul, ← mul_assoc,
          IsLocalization.mk'_spec _ c ⟨U t ^ m, _⟩, ← map_mul, hq]
      exists_of_eq := fun {p q} h => by
        rw [halg, halg] at h
        obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (U t)) h
        refine ⟨⟨Polynomial.X ^ k, k, rfl⟩, polyU_injective t ?_⟩
        simpa only [map_mul, map_pow, Polynomial.aeval_X] using hk }
  exact ModelSmooth.isStandardSmoothOfRelativeDimension_one_of_isLocalization_away_X W (Localization.Away (U t))

end awayU

section awayV

private theorem isStandardSmoothOfRelativeDimension_one_awayV [Nontrivial W] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 W (Localization.Away (V t)) := by
  letI alg : Algebra W[X] (Localization.Away (V t)) :=
    ((algebraMap (CrossingQuotient W t) (Localization.Away (V t))).comp (polyV t).toRingHom).toAlgebra
  letI smulAlg : SMul W[X] (Localization.Away (V t)) := alg.toSMul
  have halg : ∀ q : W[X], algebraMap W[X] (Localization.Away (V t)) q =
      algebraMap (CrossingQuotient W t) _ (polyV t q) := fun q => rfl
  haveI : IsScalarTower W W[X] (Localization.Away (V t)) :=
    IsScalarTower.of_algebraMap_eq (R := W) (S := W[X]) (A := Localization.Away (V t)) fun w => by
      rw [halg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization.Away (Polynomial.X : W[X]) (Localization.Away (V t)) :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        rw [halg, map_pow, Polynomial.aeval_X, map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit (V t)).pow n
      surj := fun z => by
        obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (V t)) z
        obtain ⟨n, q, hq⟩ := exists_mul_V_pow_eq_polyV t c
        refine ⟨⟨q, ⟨Polynomial.X ^ (m + n), _, rfl⟩⟩, ?_⟩
        show IsLocalization.mk' _ c ⟨V t ^ m, _⟩ * algebraMap W[X] _ (Polynomial.X ^ (m + n)) = algebraMap W[X] _ q
        rw [halg, halg, map_pow, Polynomial.aeval_X, pow_add, map_mul, ← mul_assoc,
          IsLocalization.mk'_spec _ c ⟨V t ^ m, _⟩, ← map_mul, hq]
      exists_of_eq := fun {p q} h => by
        rw [halg, halg] at h
        obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (V t)) h
        refine ⟨⟨Polynomial.X ^ k, k, rfl⟩, polyV_injective t ?_⟩
        simpa only [map_mul, map_pow, Polynomial.aeval_X] using hk }
  exact ModelSmooth.isStandardSmoothOfRelativeDimension_one_of_isLocalization_away_X W (Localization.Away (V t))

end awayV

end MvPolynomial.CrossingQuotient

namespace MvPolynomial
p2m_export "MvPolynomial" "X map coeff R aeval_X ext support aeval_def algebraMap_apply comap algebraMap_eq C monomial coeff_zero sum_def notMem_support_iff aeval_C induction_on aeval CrossingQuotient.Resolution CrossingQuotient.Resolution.exists_ι_apply_eq CrossingQuotient.Resolution.toCrossing CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.Resolution.isProper_toCrossing"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.exists_ι_apply_eq Resolution.toCrossing Resolution.toSpec U V U_mul_V lift mk mk_surjective monomial monomial_natCast monomial_neg_natCast originIdeal linearIndependent_monomial_and_span_eq_top Resolution.isProper_toCrossing"
p2m_open "MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W)

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry TopologicalSpace"

noncomputable section

private abbrev _root_.MvPolynomial.CrossingQuotient.D {R : Type u} [CommRing R] (g : R) : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen g

p2m_export "MvPolynomial.CrossingQuotient" "D"

private theorem smoothOfRelativeDimension_one_basicOpen_ι_comp {R : Type u} [CommRing R] [Algebra W R] (g : R)
    (h : Algebra.IsStandardSmoothOfRelativeDimension 1 W (Localization.Away g)) :
    SmoothOfRelativeDimension 1
      ((D g).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap W R))) := by
  let u : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
  let eI := IsOpenImmersion.isoOfRangeEq u (D g).ι
    (by rw [Scheme.Opens.range_ι]; exact PrimeSpectrum.localization_away_comap_range (Localization.Away g) g)
  have hfac : (D g).ι = eI.inv ≫ u :=
    (IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _).symm
  haveI hu : SmoothOfRelativeDimension 1 (u ≫ Spec.map (CommRingCat.ofHom (algebraMap W R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq W R (Localization.Away g)]
    refine HasRingHomProperty.Spec_iff.mpr ?_
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr h
  rw [hfac, Category.assoc]
  show SmoothOfRelativeDimension (0 + 1) (eI.inv ≫ u ≫ Spec.map (CommRingCat.ofHom (algebraMap W R)))
  infer_instance

private theorem smoothOfRelativeDimension_one_basicOpen_U [Nontrivial W] :
    SmoothOfRelativeDimension 1
      ((D (U t)).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t)))) :=
  smoothOfRelativeDimension_one_basicOpen_ι_comp (U t) (isStandardSmoothOfRelativeDimension_one_awayU t)

private theorem smoothOfRelativeDimension_one_basicOpen_V [Nontrivial W] :
    SmoothOfRelativeDimension 1
      ((D (V t)).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t)))) :=
  smoothOfRelativeDimension_one_basicOpen_ι_comp (V t) (isStandardSmoothOfRelativeDimension_one_awayV t)

namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq toCrossing toSpec ι_toSpec origin eq_origin_pt_of_mem isProper_toCrossing"
p2m_open "MvPolynomial.CrossingQuotient.Resolution"

variable (e : ℕ)

private def offOrigins : (Resolution t e).Opens :=
  ⨆ i : Fin e, (ι t e i) ''ᵁ (D (U t) ⊔ D (V t))

private theorem ι_apply_mem_offOrigins {i : Fin e} {y : chartScheme t} (hy : U t ∉ y.asIdeal ∨ V t ∉ y.asIdeal) :
    ι t e i y ∈ offOrigins t e :=
  Opens.mem_iSup.mpr ⟨i, y, hy, rfl⟩

private theorem ι_apply_mem_offOrigins_of_not {i : Fin e} {y : chartScheme t} (hy : ¬ (U t ∈ y.asIdeal ∧ V t ∈ y.asIdeal)) :
    ι t e i y ∈ offOrigins t e :=
  ι_apply_mem_offOrigins t e (not_and_or.mp hy)

private abbrev gen (b : Bool) : CrossingQuotient W t := cond b (U t) (V t)

private theorem range_basicOpen_ι_ι_subset (i : Fin e) (b : Bool) :
    Set.range ((D (gen t b)).ι ≫ ι t e i) ⊆
      Set.range (offOrigins t e).ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  refine ι_apply_mem_offOrigins t e ?_
  cases b
  · exact Or.inr z.2
  · exact Or.inl z.2

private def piece (i : Fin e) (b : Bool) :
    ((D (gen t b)) : Scheme.{u}) ⟶ (offOrigins t e : Scheme.{u}) :=
  IsOpenImmersion.lift (offOrigins t e).ι ((D (gen t b)).ι ≫ ι t e i)
    (range_basicOpen_ι_ι_subset t e i b)

@[reassoc]
private theorem piece_ι (i : Fin e) (b : Bool) :
    piece t e i b ≫ (offOrigins t e).ι = (D (gen t b)).ι ≫ ι t e i :=
  IsOpenImmersion.lift_fac _ _ _

private scoped instance (i : Fin e) (b : Bool) : IsOpenImmersion (piece t e i b) := by
  dsimp only [piece]; infer_instance

private def offOriginsCover : (offOrigins t e : Scheme.{u}).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin e × Bool) _ (fun p => piece t e p.1 p.2) (by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨y, hy, rfl⟩ := hi
    have key : ∀ (b : Bool) (hb : y ∈ (D (gen t b))),
        ∃ z, (piece t e i b).base z = ⟨ι t e i y, hx⟩ := fun b hb => by
      refine ⟨⟨y, hb⟩, (offOrigins t e).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, piece_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply]
    rcases hy with hU | hV
    · obtain ⟨z, hz⟩ := key true hU
      exact ⟨⟨i, true⟩, z, hz⟩
    · obtain ⟨z, hz⟩ := key false hV
      exact ⟨⟨i, false⟩, z, hz⟩)

private theorem smoothOfRelativeDimension_one_offOrigins [Nontrivial W] :
    SmoothOfRelativeDimension 1 ((offOrigins t e).ι ≫ toSpec t e) := by
  refine IsZariskiLocalAtSource.of_openCover (offOriginsCover t e) fun p => ?_
  obtain ⟨i, b⟩ := p
  show SmoothOfRelativeDimension 1 (piece t e i b ≫ (offOrigins t e).ι ≫ toSpec t e)
  rw [piece_ι_assoc, ι_toSpec]
  cases b
  · exact smoothOfRelativeDimension_one_basicOpen_V t
  · exact smoothOfRelativeDimension_one_basicOpen_U t

end Resolution
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution"

end
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution"

end MvPolynomial.CrossingQuotient
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient"
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial"

section W6dGeneric

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift SmoothOfRelativeDimension.smooth Scheme.Hom.preimage_smoothLocus_eq SmoothOfRelativeDimension IsOpenImmersion.isoOfRangeEq_inv_fac IsProper morphismRestrict_ι Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff IsZariskiLocalAtSource.of_openCover Scheme.Hom.smoothLocus Scheme.Pullback.range_fst isPullback_morphismRestrict LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Spec.map Scheme Smooth IsZariskiLocalAtSource IsOpenImmersion Scheme.Hom.comp_base Flat smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Hom.smoothLocus_eq_top HasRingHomProperty.Spec_iff HasRingHomProperty.iff_of_source_openCover IsOpenImmersion.isoOfRangeEq Scheme.Cover.mkOfCovers Scheme.Hom.mem_smoothLocus Etale Scheme.Opens.ι_apply smoothOfRelativeDimension_comp Scheme.Opens smooth_isStableUnderBaseChange LocallyOfFinitePresentation Flat.generalizingMap Scheme.Pullback.exists_preimage_pullback HasRingHomProperty IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.Cover Scheme.ΓSpecIso smoothOfRelativeDimension_of_irreducibleSpace Scheme.Hom.smoothLocus_le_preimage_of_isPullback Scheme.Hom.preimage_smoothLocus_le_of_isPullback"
p2m_open "AlgebraicGeometry"

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.preimage_smoothLocus_eq Opens.range_ι Hom mk Hom.smoothLocus_eq_top_iff Γ Hom.smoothLocus Pullback.range_fst Hom.stalkMap_comp OpenCover Hom.comp_base affineCover Hom.smoothLocus_eq_top basicOpen Cover.mkOfCovers Hom.mem_smoothLocus Opens.ι_apply Opens residue le_iff_specializes Pullback.exists_preimage_pullback Hom.comp_apply Cover ΓSpecIso Hom.smoothLocus_le_preimage_of_isPullback Hom.preimage_smoothLocus_le_of_isPullback" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "image preimage_smoothLocus_eq isOpenEmbedding smoothLocus_eq_top_iff smoothLocus injective surjective mk stalkMap_comp stalkMap comp_base comp_app smoothLocus_eq_top cover residueFieldMap mem_smoothLocus ker comp_apply smoothLocus_le_preimage_of_isPullback preimage_smoothLocus_le_of_isPullback" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private scoped instance Scheme.Hom.smooth_smoothLocus_ι_comp [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
  intro x _
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact x.2

p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom"
namespace Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem _root_.AlgebraicGeometry.Scheme.Hom.le_smoothLocus_of_smooth [LocallyOfFinitePresentation f] (V : X.Opens) [Smooth (V.ι ≫ f)] :
    V ≤ f.smoothLocus := by
  intro x hx
  have h : (⟨x, hx⟩ : V) ∈ (V.ι ≫ f).smoothLocus := by rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at h
  exact h

end Scheme.Hom
p2m_export "AlgebraicGeometry" "Scheme.Hom.le_smoothLocus_of_smooth"
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem Scheme.Hom.mem_smoothLocus_of_mem_of_smooth [LocallyOfFinitePresentation f] (V : X.Opens) (hV : Smooth (V.ι ≫ f))
    (x : X) (hx : x ∈ V) : x ∈ f.smoothLocus :=
  f.le_smoothLocus_of_smooth V hx

private theorem smoothOfRelativeDimension_smoothLocus_ι_comp (n : ℕ) [LocallyOfFinitePresentation f] [IrreducibleSpace X]
    (V : X.Opens) (hV : (V : Set X).Nonempty) [SmoothOfRelativeDimension n (V.ι ≫ f)] :
    SmoothOfRelativeDimension n (f.smoothLocus.ι ≫ f) := by
  haveI : Smooth (V.ι ≫ f) := SmoothOfRelativeDimension.smooth n _
  have hle : V ≤ f.smoothLocus := f.le_smoothLocus_of_smooth V

  have hne : (f.smoothLocus : Set X).Nonempty := hV.mono hle
  haveI : IrreducibleSpace f.smoothLocus :=
    Subtype.irreducibleSpace ⟨hne, (IrreducibleSpace.isIrreducible_univ X).2.open_subset f.smoothLocus.2 (Set.subset_univ _)⟩

  let V' : (f.smoothLocus : Scheme.{u}).Opens := f.smoothLocus.ι ⁻¹ᵁ V
  have hV' : (V' : Set f.smoothLocus).Nonempty := by
    obtain ⟨x, hx⟩ := hV
    exact ⟨⟨x, hle hx⟩, hx⟩
  haveI : SmoothOfRelativeDimension n (V'.ι ≫ f.smoothLocus.ι ≫ f) := by
    have h : V'.ι ≫ f.smoothLocus.ι ≫ f = (f.smoothLocus.ι ∣_ V) ≫ (V.ι ≫ f) := by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    rw [h]
    have : SmoothOfRelativeDimension (0 + n) ((f.smoothLocus.ι ∣_ V) ≫ (V.ι ≫ f)) :=
      smoothOfRelativeDimension_comp 0 n (f := f.smoothLocus.ι ∣_ V) (V.ι ≫ f)
    simpa using this
  exact smoothOfRelativeDimension_of_irreducibleSpace n (f.smoothLocus.ι ≫ f) V' hV'

private theorem locallyOfFinitePresentation_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType c] : LocallyOfFinitePresentation c := by
  have hft := (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType) (f := c) C.affineCover).mp
    inferInstance
  refine (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFinitePresentation) (f := c) C.affineCover).mpr
    fun i => ?_

  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  exact RingHom.FinitePresentation.of_finiteType.mp (hft i)

namespace Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem _root_.AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_comp_of_smooth {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) [Smooth g]
    [LocallyOfFinitePresentation h] (x : X) (hx : g.base x ∈ h.smoothLocus) :
    x ∈ (g ≫ h).smoothLocus := by
  rw [Scheme.Hom.mem_smoothLocus] at hx ⊢
  have hg : (g.stalkMap x).hom.FormallySmooth := by
    have : x ∈ g.smoothLocus := by rw [Scheme.Hom.smoothLocus_eq_top]; trivial
    exact this
  rw [Scheme.Hom.stalkMap_comp]
  change (CommRingCat.Hom.hom (g.stalkMap x) |>.comp (CommRingCat.Hom.hom (h.stalkMap (g.base x)))).FormallySmooth
  exact RingHom.FormallySmooth.comp hx hg

end Scheme.Hom
p2m_export "AlgebraicGeometry" "Scheme.Hom.mem_smoothLocus_comp_of_smooth"
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem Scheme.Hom.mem_smoothLocus_of_fac {Z T : Scheme.{u}} (f : T ⟶ Z) [LocallyOfFinitePresentation f]
    (ι : X ⟶ T) [IsOpenImmersion ι] (g : X ⟶ Y) (h : Y ⟶ Z) [Smooth g] [LocallyOfFinitePresentation h]
    (fac : ι ≫ f = g ≫ h) (x : X) (hx : g.base x ∈ h.smoothLocus) :
    ι.base x ∈ f.smoothLocus := by
  have h1 : x ∈ (g ≫ h).smoothLocus := g.mem_smoothLocus_comp_of_smooth h x hx
  have h3 : x ∈ (ι ≫ f).smoothLocus := by
    have key : ∀ (k : X ⟶ Z) [LocallyOfFinitePresentation k], k = g ≫ h → x ∈ k.smoothLocus := by
      intro k _ hk; subst hk; exact h1
    exact key (ι ≫ f) fac
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at h3
  exact h3

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem Scheme.Hom.mem_smoothLocus_of_fac' {Z T : Scheme.{u}} (f : T ⟶ Z) (hf : LocallyOfFinitePresentation f)
    (ι : X ⟶ T) (hι : IsOpenImmersion ι) (g : X ⟶ Y) (h : Y ⟶ Z) (hg : Smooth g) (hh : LocallyOfFinitePresentation h)
    (fac : ι ≫ f = g ≫ h) (x : X) (hx : g.base x ∈ h.smoothLocus) :
    ι.base x ∈ f.smoothLocus :=
  Scheme.Hom.mem_smoothLocus_of_fac f ι g h fac x hx

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"
end W6dGeneric
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"

namespace V3Glue
p2m_export "V3Glue" "LevelSite.Node ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "xU vertex eq_liftY_of_g_eq edgePt' Y q a j toGlueInput hq g toB_eq interior_setOf_q_eq πX Res X0 U σ mk S B ρ x thick f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private theorem _root_.V3Glue.ChartInput.ιY_toDR_πX (n : N) :
    C.toGlueInput.ιY n ≫ C.toGlueInput.toDR ≫ C.πX = C.g n ≫ (C.ρ n ≫ C.σ n) := by
  rw [← Category.assoc, C.toGlueInput.ιY_toDR, Category.assoc]
  change C.q n ≫ (C.U n).ι ≫ C.πX = _
  rw [← C.toB_eq]
  rfl

p2m_export "V3Glue.ChartInput" "ιY_toDR_πX"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"

namespace V3Glue
p2m_export "V3Glue" "LevelSite.Node ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "xU vertex eq_liftY_of_g_eq edgePt' Y q a j toGlueInput hq g toB_eq interior_setOf_q_eq πX Res X0 U σ mk S B ρ x thick f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

private theorem _root_.V3Glue.ChartInput.ιY_eq_edgePt'_of_g_eq_oRes (n : N) (d : Fin (C.thick n)) (y : C.Y n) (hy : C.g n y = oRes n d) :
    C.toGlueInput.ιY n y = C.edgePt' hRF oRes hoRes n d := by
  rw [C.eq_liftY_of_g_eq n (hRF n) (oRes n d) (hoRes n d) y hy]; rfl

p2m_export "V3Glue.ChartInput" "ιY_eq_edgePt'_of_g_eq_oRes"

private theorem _root_.V3Glue.ChartInput.exists_edgePt'_eq_of_g_eq_oRes (n : N) (y : C.Y n) (hy : C.g n y ∈ Set.range (oRes n)) :
    ∃ d : Fin (C.thick n), C.toGlueInput.ιY n y = C.edgePt' hRF oRes hoRes n d := by
  obtain ⟨d, hd⟩ := hy
  exact ⟨d, C.ιY_eq_edgePt'_of_g_eq_oRes hRF oRes hoRes n d y hd.symm⟩

p2m_export "V3Glue.ChartInput" "exists_edgePt'_eq_of_g_eq_oRes"

private theorem _root_.V3Glue.ChartInput.g_not_mem_range_oRes_of_ne_edgePt' (n : N) (y : C.Y n)
    (hne : ∀ d : Fin (C.thick n), C.toGlueInput.ιY n y ≠ C.edgePt' hRF oRes hoRes n d) :
    C.g n y ∉ Set.range (oRes n) := fun h => by
  obtain ⟨d, hd⟩ := C.exists_edgePt'_eq_of_g_eq_oRes hRF oRes hoRes n y h
  exact hne d hd

p2m_export "V3Glue.ChartInput" "g_not_mem_range_oRes_of_ne_edgePt'"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"

namespace MvPolynomial
p2m_export "MvPolynomial" "X map coeff R aeval_X ext support aeval_def algebraMap_apply comap algebraMap_eq C monomial coeff_zero sum_def notMem_support_iff aeval_C induction_on aeval CrossingQuotient.Resolution CrossingQuotient.Resolution.exists_ι_apply_eq CrossingQuotient.Resolution.toCrossing CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.Resolution.isProper_toCrossing"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.exists_ι_apply_eq Resolution.toCrossing Resolution.toSpec U V U_mul_V lift mk mk_surjective monomial monomial_natCast monomial_neg_natCast originIdeal linearIndependent_monomial_and_span_eq_top Resolution.isProper_toCrossing"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq toCrossing toSpec ι_toSpec origin eq_origin_pt_of_mem isProper_toCrossing"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) (ht : t ∈ 𝔭)

private theorem ι_apply_eq_origin_of_U_mem_of_V_mem [𝔭.IsMaximal] (h𝔭t : 𝔭 ≤ Ideal.span {t}) (i : Fin e)
    (P : chartScheme t) (hU : U t ∈ P.asIdeal) (hV : V t ∈ P.asIdeal) :
    ι t e i P = origin t e 𝔭 ht i := by
  have htP : algebraMap W (CrossingQuotient W t) t ∈ P.asIdeal := by
    rw [← U_mul_V]; exact P.asIdeal.mul_mem_left _ hV
  have h : P = ⟨originIdeal t 𝔭 ht, inferInstance⟩ :=
    eq_origin_pt_of_mem t 𝔭 ht hU hV (fun w hw => by
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (h𝔭t hw)
      rw [map_mul]
      exact P.asIdeal.mul_mem_left _ htP)
  subst h
  rfl

private theorem ι_apply_mem_range_origin_of_U_mem_of_V_mem [𝔭.IsMaximal] (h𝔭t : 𝔭 ≤ Ideal.span {t}) (i : Fin e)
    (P : chartScheme t) (hU : U t ∈ P.asIdeal) (hV : V t ∈ P.asIdeal) :
    ι t e i P ∈ Set.range (origin t e 𝔭 ht) :=
  ⟨i, (ι_apply_eq_origin_of_U_mem_of_V_mem t e 𝔭 ht h𝔭t i P hU hV).symm⟩

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry"

private theorem isLocalizationAway_natCast_rat (q : ℕ) [hq : Fact q.Prime] :
    IsLocalization.Away (((q : ℕ) : ModularCurve.DRLevel.R q)) ℚ where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    simp only [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hq.out.ne_zero)
  surj := by
    intro z
    obtain ⟨a, m, hqm, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd z.den_nz q hq.out.one_lt.ne'
    have hm0 : (m : ℚ) ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; simp at hden
      exact Nat.cast_ne_zero.mpr this

    have hz : z * (q : ℚ) ^ a = (z.num : ℚ) / m := by
      have h1 : z = z.num / z.den := (Rat.num_div_den z).symm
      have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
      rw [eq_div_iff hm0]
      conv_lhs => rw [h1]
      rw [hden]; push_cast
      field_simp

    have hmem : ((z.num : ℚ) / m) ∈ GaloisRep.ratLocalizedAt q := by
      show ((z.num : ℚ) / m).den.Coprime q
      have hdvd : (((z.num : ℚ) / m).den : ℤ) ∣ (m : ℤ) := by
        have := Rat.den_dvd z.num m
        rwa [Rat.divInt_eq_div, Int.cast_natCast] at this
      have hdvd' : ((z.num : ℚ) / m).den ∣ m := by exact_mod_cast hdvd
      have hcop : m.Coprime q := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hq.out).mpr hqm)
      exact Nat.Coprime.coprime_dvd_left hdvd' hcop
    refine ⟨⟨⟨_, hmem⟩, ⟨((q : ℕ) : ModularCurve.DRLevel.R q) ^ a, a, rfl⟩⟩, ?_⟩
    simp only [map_pow, map_natCast]
    rw [hz]
    rfl
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa using Subtype.val_injective h⟩

namespace V3AsmLevel
p2m_export "V3AsmLevel" "πX SiteHyps R C D Y toDR toBase hq mem_X0_iff width hRF p_mem_maximalIdeal ξ oRes hoRes comp edgePt"
p2m_open "V3AsmLevel"

p2m_open "ModularCurve MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient TopologicalSpace"

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O) (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)}) (H : SiteHyps 𝔛 O ρO κ toκ)

include 𝔛 in
private theorem isProper_πX' : IsProper (πX (N₀ := N₀) O ρO) := by
  haveI := 𝔛.isProper
  exact MorphismProperty.pullback_snd _ _ inferInstance

include 𝔛 in
private theorem flat_πX' : Flat (πX (N₀ := N₀) O ρO) := by
  haveI := 𝔛.flat
  exact MorphismProperty.pullback_snd _ _ inferInstance

include hϖ in
private theorem p_ne_zero' : ((q : ℕ) : O) ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field O
  rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl]

private theorem etale_f' (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) : Etale ((C 𝔛 O ρO κ toκ hϖ H).f n) := by
  haveI := H.nodeFinite
  exact (R 𝔛 O ρO κ toκ hϖ H).etale_toChartInput_f _ n

private theorem toDR_proper' : IsProper (toDR 𝔛 O ρO κ toκ hϖ H) :=
  (D 𝔛 O ρO κ toκ hϖ H).isProper_toDR (hq 𝔛 O ρO κ toκ hϖ H) (fun n => show IsProper ((C 𝔛 O ρO κ toκ hϖ H).q n) from inferInstance)

private theorem isProper' : IsProper (toBase 𝔛 O ρO κ toκ hϖ H) := by
  haveI := toDR_proper' 𝔛 O ρO κ toκ hϖ H
  haveI := isProper_πX' 𝔛 O ρO
  show IsProper (toDR 𝔛 O ρO κ toκ hϖ H ≫ πX (N₀ := N₀) O ρO)
  infer_instance

include 𝔛 hϖ in
private theorem isIntegral_XO' : IsIntegral (DRLevel.XO (N₀ := N₀) ρO) :=
  ModularCurve.DRModelPackageLevel.isIntegral_pullback_toBase_specMap N₀ q hqN 𝔛 O hϖ ρO

private theorem snd_preimage_basicOpen_le_X0' :
    (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) ≤
      (D 𝔛 O ρO κ toκ hϖ H).X0 := by
  intro x hx
  refine (mem_X0_iff 𝔛 O ρO κ toκ hϖ H x).mpr fun n hn => ?_
  subst hn
  exact ModularCurve.DRLevel.bcMap_apply_notMem_preimage_basicOpen N₀ q O ρO κ toκ _ hx

private theorem nonempty_X0' : Nonempty ((D 𝔛 O ρO κ toκ hϖ H).X0) := by
  haveI := isIntegral_XO' 𝔛 O ρO hϖ
  haveI := flat_πX' 𝔛 O ρO
  obtain ⟨x⟩ := (inferInstance : Nonempty ↥(DRLevel.XO (N₀ := N₀) ρO))
  let ξ : ↥(Spec (CommRingCat.of O)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ : ξ ⤳ (πX (N₀ := N₀) O ρO).base x := (PrimeSpectrum.le_iff_specializes ξ ((πX (N₀ := N₀) O ρO).base x)).mp bot_le
  obtain ⟨x', -, hx'⟩ := Flat.generalizingMap (πX (N₀ := N₀) O ρO) hξ
  refine ⟨⟨x', snd_preimage_basicOpen_le_X0' 𝔛 O ρO κ toκ hϖ H ?_⟩⟩
  show (πX (N₀ := N₀) O ρO).base x' ∈ PrimeSpectrum.basicOpen ((q : ℕ) : O)
  rw [show (πX (N₀ := N₀) O ρO).base x' = ξ from hx']
  show ((q : ℕ) : O) ∉ (⊥ : Ideal O)
  rw [Ideal.mem_bot]
  exact p_ne_zero' O hϖ

private theorem irreducibleSpace_Y : IrreducibleSpace (Y 𝔛 O ρO κ toκ hϖ H) := by
  haveI := isIntegral_XO' 𝔛 O ρO hϖ
  haveI := nonempty_X0' 𝔛 O ρO κ toκ hϖ H
  haveI := H.nodeFinite
  haveI : Fintype (V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) := Fintype.ofFinite _
  exact (D 𝔛 O ρO κ toκ hϖ H).irreducibleSpace_glued (hq 𝔛 O ρO κ toκ hϖ H) (fun n => H.hxcl n)
    (fun n => (D 𝔛 O ρO κ toκ hϖ H).interior_preimage_toDR_x_eq_empty (hq 𝔛 O ρO κ toκ hϖ H) n ((C 𝔛 O ρO κ toκ hϖ H).interior_setOf_q_eq n))

private theorem fst_preimage_smoothLocus_le_X0' :
    pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) ⁻¹ᵁ 𝔛.smoothLocus ≤ (D 𝔛 O ρO κ toκ hϖ H).X0 := by
  intro x hx
  refine (mem_X0_iff 𝔛 O ρO κ toκ hϖ H x).mpr fun n hn => ?_
  subst hn
  let y := (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0).base n
  have hy : y = (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0).base n := rfl
  have hyboth : y ∈ Set.range ⇑(𝔛.comp κ (toκ.comp ρO) 0).base ∧ y ∈ Set.range ⇑(𝔛.comp κ (toκ.comp ρO) 1).base := by
    refine ⟨⟨(pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, rfl⟩,
      ⟨(pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, ?_⟩⟩
    rw [hy, pullback.condition]
    rfl
  apply (ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
    N₀ q hqN 𝔛 κ (toκ.comp ρO) y).not.mpr (not_not.mpr hyboth)
  have hfst : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q)
      (Spec.map (CommRingCat.ofHom ρO)) = pullback.fst (DRLevel.toBase N₀ q) _ := by
    rw [DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
  change (pullback.fst (DRLevel.toBase N₀ q) _).base y ∈ 𝔛.smoothLocus
  rw [← hfst]
  exact hx

private theorem toDR_iso_smoothLocus' :
    IsIso (toDR 𝔛 O ρO κ toκ hϖ H ∣_ (pullback.fst (DRLevel.toBase N₀ q) _ ⁻¹ᵁ 𝔛.smoothLocus)) :=
  (D 𝔛 O ρO κ toκ hϖ H).isIso_toDR_restrict (hq 𝔛 O ρO κ toκ hϖ H) (fst_preimage_smoothLocus_le_X0' 𝔛 O ρO κ toκ hϖ H)

local notation "𝕐" => Y 𝔛 O ρO κ toκ hϖ H
local notation "𝕎" => width 𝔛 O ρO κ toκ hϖ H

private scoped instance toBase_lfp : LocallyOfFinitePresentation (toBase 𝔛 O ρO κ toκ hϖ H) := by
  haveI := isProper' 𝔛 O ρO κ toκ hϖ H
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_isNoetherianRing (toBase 𝔛 O ρO κ toκ hϖ H)

private def smoothOffEdges : (𝕐).Opens := (toBase 𝔛 O ρO κ toκ hϖ H).smoothLocus

private def Vsm : (𝕐).Opens :=
  toDR 𝔛 O ρO κ toκ hϖ H ⁻¹ᵁ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) ⁻¹ᵁ 𝔛.smoothLocus)

private theorem smoothOfRelativeDimension_one_Vsm : SmoothOfRelativeDimension 1 ((Vsm 𝔛 O ρO κ toκ hϖ H).ι ≫ toBase 𝔛 O ρO κ toκ hϖ H) := by

  let c := DRLevel.toBase N₀ q
  let s := Spec.map (CommRingCat.ofHom ρO)
  let W : (DRLevel.XO (N₀ := N₀) ρO).Opens := pullback.fst c s ⁻¹ᵁ 𝔛.smoothLocus
  haveI := 𝔛.smoothLocus_relDim
  have hW : SmoothOfRelativeDimension 1 (W.ι ≫ πX (N₀ := N₀) O ρO) := by
    have hsq : IsPullback ((pullback.fst c s) ∣_ 𝔛.smoothLocus) W.ι 𝔛.smoothLocus.ι (pullback.fst c s) :=
      isPullback_morphismRestrict _ _
    have hbig : IsPullback ((pullback.fst c s) ∣_ 𝔛.smoothLocus) (W.ι ≫ πX (N₀ := N₀) O ρO) (𝔛.smoothLocus.ι ≫ c) s :=
      hsq.paste_vert (IsPullback.of_hasPullback c s)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hbig inferInstance

  haveI : IsIso (toDR 𝔛 O ρO κ toκ hϖ H ∣_ W) := toDR_iso_smoothLocus' 𝔛 O ρO κ toκ hϖ H
  have hfac : (Vsm 𝔛 O ρO κ toκ hϖ H).ι ≫ toBase 𝔛 O ρO κ toκ hϖ H = (toDR 𝔛 O ρO κ toκ hϖ H ∣_ W) ≫ (W.ι ≫ πX (N₀ := N₀) O ρO) := by
    change (toDR 𝔛 O ρO κ toκ hϖ H ⁻¹ᵁ W).ι ≫ toDR 𝔛 O ρO κ toκ hϖ H ≫ πX (N₀ := N₀) O ρO = _
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rw [hfac]
  have : SmoothOfRelativeDimension (0 + 1) ((toDR 𝔛 O ρO κ toκ hϖ H ∣_ W) ≫ (W.ι ≫ πX (N₀ := N₀) O ρO)) :=
    smoothOfRelativeDimension_comp 0 1 (f := toDR 𝔛 O ρO κ toκ hϖ H ∣_ W) (W.ι ≫ πX (N₀ := N₀) O ρO)
  first | simpa using this | (simp at this; exact this) | exact this

private theorem Vsm_nonempty : ((Vsm 𝔛 O ρO κ toκ hϖ H : (𝕐).Opens) : Set 𝕐).Nonempty := by
  classical
  let c := DRLevel.toBase N₀ q
  let s := Spec.map (CommRingCat.ofHom ρO)
  let W : (DRLevel.XO (N₀ := N₀) ρO).Opens := pullback.fst c s ⁻¹ᵁ 𝔛.smoothLocus

  haveI : Nonempty (Spec (CommRingCat.of O)) := inferInstance
  let pt : Spec (CommRingCat.of O) ⟶ DRLevel.XO (N₀ := N₀) ρO :=
    pullback.lift (s ≫ 𝔛.εinf.1) (𝟙 _) (by rw [Category.assoc, 𝔛.εinf.2, Category.comp_id, Category.id_comp])
  have hpt : ∀ t, pt.base t ∈ W := by
    intro t
    show (pullback.fst c s).base (pt.base t) ∈ 𝔛.smoothLocus
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact 𝔛.εinf_mem_smoothLocus ⟨_, rfl⟩
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of O)))

  haveI : IsIso (toDR 𝔛 O ρO κ toκ hϖ H ∣_ W) := toDR_iso_smoothLocus' 𝔛 O ρO κ toκ hϖ H
  obtain ⟨y, hy⟩ := (toDR 𝔛 O ρO κ toκ hϖ H ∣_ W).surjective ⟨pt.base t, hpt t⟩
  exact ⟨y.1, y.2⟩

private theorem smoothOffEdges_smooth : SmoothOfRelativeDimension 1 ((smoothOffEdges 𝔛 O ρO κ toκ hϖ H).ι ≫ toBase 𝔛 O ρO κ toκ hϖ H) := by
  haveI := irreducibleSpace_Y 𝔛 O ρO κ toκ hϖ H
  haveI := smoothOfRelativeDimension_one_Vsm 𝔛 O ρO κ toκ hϖ H
  exact AlgebraicGeometry.smoothOfRelativeDimension_smoothLocus_ι_comp (toBase 𝔛 O ρO κ toκ hϖ H) 1
    (Vsm 𝔛 O ρO κ toκ hϖ H) (Vsm_nonempty 𝔛 O ρO κ toκ hϖ H)

private theorem baseChangeMap_fst :
    DRLevel.bcMap ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
  rw [DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]

include hϖ in

private theorem exists_baseChangeMap_eq (x : ↥(DRLevel.XO (N₀ := N₀) ρO))
    (hx : x ∉ (πX (N₀ := N₀) O ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y, (DRLevel.bcMap (N₀ := N₀) ρO toκ).base y = x := by
  classical
  let c := DRLevel.toBase N₀ q
  let sO := Spec.map (CommRingCat.ofHom ρO)
  let sκ := Spec.map (CommRingCat.ofHom (toκ.comp ρO))
  let t := Spec.map (CommRingCat.ofHom toκ)

  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top toκ)) ?_
    rw [hϖ, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

  have hxc : ((πX (N₀ := N₀) O ρO).base x).asIdeal = IsLocalRing.maximalIdeal O := by
    have hp : ((q : ℕ) : O) ∈ ((πX (N₀ := N₀) O ρO).base x).asIdeal := by
      by_contra h
      exact hx h
    have hle : IsLocalRing.maximalIdeal O ≤ ((πX (N₀ := N₀) O ρO).base x).asIdeal := by
      rw [hϖ, Ideal.span_le, Set.singleton_subset_iff]; exact hp
    exact (IsLocalRing.le_maximalIdeal ((πX (N₀ := N₀) O ρO).base x).isPrime.ne_top).antisymm hle |>.symm ▸ rfl
  have htc : (t.base (IsLocalRing.closedPoint κ)).asIdeal = IsLocalRing.maximalIdeal O := by
    change Ideal.comap toκ (IsLocalRing.closedPoint κ).asIdeal = _
    rw [show (IsLocalRing.closedPoint κ).asIdeal = ⊥ from Ideal.eq_bot_of_prime _, ← RingHom.ker_eq_comap_bot, hker]
  have hxt : (πX (N₀ := N₀) O ρO).base x = t.base (IsLocalRing.closedPoint κ) := PrimeSpectrum.ext (hxc.trans htc.symm)

  have hsq : IsPullback (DRLevel.bcMap (N₀ := N₀) ρO toκ) (pullback.snd c sκ) (pullback.snd c sO) t := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback c sO)
    ·
      have ht : t ≫ sO = sκ := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hfst : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst c sO = pullback.fst c sκ := baseChangeMap_fst O ρO κ toκ
      rw [hfst, ht]
      exact IsPullback.of_hasPullback c sκ
    ·
      rw [DRLevel.bcMap, pullback.map, pullback.lift_snd]

  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd c sO) (g := t) x (IsLocalRing.closedPoint κ) hxt
  refine ⟨hsq.isoPullback.inv.base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hz1

include 𝔛 in

private theorem mem_smoothLocus_πX_of_mem_basicOpen [LocallyOfFinitePresentation (πX (N₀ := N₀) O ρO)] (x : ↥(DRLevel.XO (N₀ := N₀) ρO))
    (hx : x ∈ (πX (N₀ := N₀) O ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    x ∈ (πX (N₀ := N₀) O ρO).smoothLocus := by
  classical
  let c := DRLevel.toBase N₀ q
  let sO := Spec.map (CommRingCat.ofHom ρO)
  let ℓ := Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) ℚ))
  haveI : IsProper c := 𝔛.isProper
  haveI : LocallyOfFinitePresentation c := 𝔛.lfp
  haveI : IsLocalization.Away (((q : ℕ) : DRLevel.R q)) ℚ := isLocalizationAway_natCast_rat q

  have h1 : pullback.fst c sO ⁻¹ᵁ c.smoothLocus ≤ (πX (N₀ := N₀) O ρO).smoothLocus :=
    Scheme.Hom.preimage_smoothLocus_le_of_isPullback (IsPullback.of_hasPullback c sO)
  apply h1
  show (pullback.fst c sO).base x ∈ c.smoothLocus

  have hxD : c.base ((pullback.fst c sO).base x) ∈ PrimeSpectrum.basicOpen ((q : ℕ) : DRLevel.R q) := by
    have hsq := congr($(pullback.condition (f := c) (g := sO)).base x)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hsq
    rw [hsq]
    change ((q : ℕ) : DRLevel.R q) ∉ Ideal.comap ρO ((πX (N₀ := N₀) O ρO).base x).asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hx

  haveI : SmoothOfRelativeDimension 1 (pullback.snd c ℓ) := 𝔛.smooth_generic
  haveI : Smooth (pullback.snd c ℓ) := SmoothOfRelativeDimension.smooth (n := 1) (f := pullback.snd c ℓ)
  haveI : Flat ℓ := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ℚ (Submonoid.powers (((q : ℕ) : DRLevel.R q))))
  have h2 : (pullback.snd c ℓ).smoothLocus ≤ pullback.fst c ℓ ⁻¹ᵁ c.smoothLocus :=
    Scheme.Hom.smoothLocus_le_preimage_of_isPullback (IsPullback.of_hasPullback c ℓ)
  have hrange : (pullback.fst c sO).base x ∈ Set.range (pullback.fst c ℓ).base := by
    rw [Scheme.Pullback.range_fst]
    show c.base _ ∈ Set.range ℓ.base
    erw [PrimeSpectrum.localization_away_comap_range ℚ (((q : ℕ) : DRLevel.R q))]
    exact hxD
  obtain ⟨z, hz⟩ := hrange
  have hz' : z ∈ (pullback.snd c ℓ).smoothLocus := by rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  have := h2 hz'
  rw [← hz]
  exact this

private theorem πX_mem_smoothLocus_of_mem_X0 [hπ : LocallyOfFinitePresentation (πX (N₀ := N₀) O ρO)] (x : ↥(DRLevel.XO (N₀ := N₀) ρO)) (hx : x ∈ (D 𝔛 O ρO κ toκ hϖ H).X0) :
    x ∈ (πX (N₀ := N₀) O ρO).smoothLocus := by
  classical
  by_cases hgen : x ∈ (πX (N₀ := N₀) O ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
  · exact mem_smoothLocus_πX_of_mem_basicOpen 𝔛 O ρO x hgen
  ·
    obtain ⟨y, rfl⟩ := exists_baseChangeMap_eq O ρO κ toκ hϖ x hgen
    have hnot : ¬ (y ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0).base ∧ y ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1).base) := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

      obtain ⟨n, hn1, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
      have hmem := ((D 𝔛 O ρO κ toκ hϖ H).mem_X0 _).mp hx n
      apply hmem
      show (DRLevel.bcMap ρO toκ).base y =
        (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base n
      rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.comp_app, hn1, ha]
    have hsm : y ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) ⁻¹ᵁ 𝔛.smoothLocus) :=
      (ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter N₀ q hqN 𝔛 κ (toκ.comp ρO) y).mpr hnot

    let c := DRLevel.toBase N₀ q
    let s := Spec.map (CommRingCat.ofHom ρO)
    let W : (DRLevel.XO (N₀ := N₀) ρO).Opens := pullback.fst c s ⁻¹ᵁ 𝔛.smoothLocus
    have hW : (DRLevel.bcMap ρO toκ).base y ∈ W := by
      show (pullback.fst c s).base ((DRLevel.bcMap ρO toκ).base y) ∈ 𝔛.smoothLocus
      rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, baseChangeMap_fst O ρO κ toκ]
      exact hsm
    haveI := 𝔛.smoothLocus_relDim
    have hWsm : Smooth (W.ι ≫ πX (N₀ := N₀) O ρO) := by
      have hsq : IsPullback ((pullback.fst c s) ∣_ 𝔛.smoothLocus) W.ι 𝔛.smoothLocus.ι (pullback.fst c s) :=
        isPullback_morphismRestrict _ _
      have hbig : IsPullback ((pullback.fst c s) ∣_ 𝔛.smoothLocus) (W.ι ≫ πX (N₀ := N₀) O ρO) (𝔛.smoothLocus.ι ≫ c) s :=
        hsq.paste_vert (IsPullback.of_hasPullback c s)
      haveI : Smooth (𝔛.smoothLocus.ι ≫ c) := SmoothOfRelativeDimension.smooth (n := 1) (f := 𝔛.smoothLocus.ι ≫ c)
      exact smooth_isStableUnderBaseChange.of_isPullback hbig inferInstance
    exact Scheme.Hom.mem_smoothLocus_of_mem_of_smooth (πX (N₀ := N₀) O ρO) W hWsm _ hW

include 𝔛 in
private theorem πX_lfp : LocallyOfFinitePresentation (πX (N₀ := N₀) O ρO) := by
  haveI := isProper_πX' 𝔛 O ρO
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_isNoetherianRing (πX (N₀ := N₀) O ρO)

private theorem mem_smoothOffEdges_X0 (x0 : (D 𝔛 O ρO κ toκ hϖ H).X0) :
    ((D 𝔛 O ρO κ toκ hϖ H).ιX0).base x0 ∈ smoothOffEdges 𝔛 O ρO κ toκ hϖ H := by
  have fac : (D 𝔛 O ρO κ toκ hϖ H).ιX0 ≫ toBase 𝔛 O ρO κ toκ hϖ H = (D 𝔛 O ρO κ toκ hϖ H).X0.ι ≫ πX (N₀ := N₀) O ρO := by
    change (D 𝔛 O ρO κ toκ hϖ H).ιX0 ≫ toDR 𝔛 O ρO κ toκ hϖ H ≫ πX (N₀ := N₀) O ρO = _
    rw [← Category.assoc]
    erw [(D 𝔛 O ρO κ toκ hϖ H).ιX0_toDR]
  have hι : IsOpenImmersion ((D 𝔛 O ρO κ toκ hϖ H).ιX0) := by
    show IsOpenImmersion ((C 𝔛 O ρO κ toκ hϖ H).toGlueInput.ιX0)
    infer_instance
  have hgsm : Smooth ((D 𝔛 O ρO κ toκ hϖ H).X0.ι) := inferInstance
  haveI hπlfp : LocallyOfFinitePresentation (πX (N₀ := N₀) O ρO) := πX_lfp 𝔛 O ρO
  exact Scheme.Hom.mem_smoothLocus_of_fac' (toBase 𝔛 O ρO κ toκ hϖ H) inferInstance ((D 𝔛 O ρO κ toκ hϖ H).ιX0) hι
    ((D 𝔛 O ρO κ toκ hϖ H).X0.ι) (πX (N₀ := N₀) O ρO) hgsm hπlfp fac x0
    (πX_mem_smoothLocus_of_mem_X0 𝔛 O ρO κ toκ hϖ H (hπ := hπlfp) x0.1 x0.2)

private theorem g_mem_smoothLocus_of_ne_edgePt (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (yn : (D 𝔛 O ρO κ toκ hϖ H).Y n)
    [LocallyOfFinitePresentation ((C 𝔛 O ρO κ toκ hϖ H).ρ n ≫ (C 𝔛 O ρO κ toκ hϖ H).σ n)]
    (hy : ∀ (m : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (d : Fin (𝕎 m)), ((D 𝔛 O ρO κ toκ hϖ H).ιY n).base yn ≠ edgePt 𝔛 O ρO κ toκ hϖ H m d) :
    ((C 𝔛 O ρO κ toκ hϖ H).g n).base yn ∈ ((C 𝔛 O ρO κ toκ hϖ H).ρ n ≫ (C 𝔛 O ρO κ toκ hϖ H).σ n).smoothLocus := by

  have hσ : (C 𝔛 O ρO κ toκ hϖ H).ρ n ≫ (C 𝔛 O ρO κ toκ hϖ H).σ n =
      MvPolynomial.CrossingQuotient.Resolution.toSpec ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n) := by
    rfl

  have hoff : ∀ z, z ∈ MvPolynomial.CrossingQuotient.Resolution.offOrigins ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n) →
      z ∈ ((C 𝔛 O ρO κ toκ hϖ H).ρ n ≫ (C 𝔛 O ρO κ toκ hϖ H).σ n).smoothLocus := by
    intro z hz
    have key : ∀ (k : (C 𝔛 O ρO κ toκ hϖ H).Res n ⟶ (C 𝔛 O ρO κ toκ hϖ H).B) (hk_lfp : LocallyOfFinitePresentation k),
        k = MvPolynomial.CrossingQuotient.Resolution.toSpec ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n) → z ∈ @Scheme.Hom.smoothLocus _ _ k hk_lfp := by
      intro k hk_lfp hk
      subst hk
      have hsm : SmoothOfRelativeDimension 1 ((MvPolynomial.CrossingQuotient.Resolution.offOrigins ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)).ι ≫
          MvPolynomial.CrossingQuotient.Resolution.toSpec ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)) :=
        MvPolynomial.CrossingQuotient.Resolution.smoothOfRelativeDimension_one_offOrigins ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)
      haveI := hsm
      haveI : Smooth ((MvPolynomial.CrossingQuotient.Resolution.offOrigins ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)).ι ≫
          MvPolynomial.CrossingQuotient.Resolution.toSpec ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)) :=
        SmoothOfRelativeDimension.smooth (n := 1)
          (f := (MvPolynomial.CrossingQuotient.Resolution.offOrigins ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)).ι ≫
            MvPolynomial.CrossingQuotient.Resolution.toSpec ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n))
      exact @Scheme.Hom.mem_smoothLocus_of_mem_of_smooth _ _ (MvPolynomial.CrossingQuotient.Resolution.toSpec ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n))
        hk_lfp (MvPolynomial.CrossingQuotient.Resolution.offOrigins ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)) this z hz
    exact key _ inferInstance hσ

  obtain ⟨i, z, hz⟩ := MvPolynomial.CrossingQuotient.Resolution.exists_ι_apply_eq ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n) (((C 𝔛 O ρO κ toκ hϖ H).g n).base yn)
  by_cases horig : MvPolynomial.CrossingQuotient.U ((q : ℕ) : O) ∈ z.asIdeal ∧ MvPolynomial.CrossingQuotient.V ((q : ℕ) : O) ∈ z.asIdeal
  ·
    exfalso
    have hmem : ((C 𝔛 O ρO κ toκ hϖ H).g n).base yn ∈ Set.range (oRes 𝔛 O ρO κ toκ hϖ H n) := by
      rw [← hz]
      exact MvPolynomial.CrossingQuotient.Resolution.ι_apply_mem_range_origin_of_U_mem_of_V_mem ((q : ℕ) : O)
        ((C 𝔛 O ρO κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal O hϖ) (hϖ ▸ le_rfl) i z horig.1 horig.2
    exact (C 𝔛 O ρO κ toκ hϖ H).g_not_mem_range_oRes_of_ne_edgePt' (hRF 𝔛 O ρO κ toκ hϖ H) (oRes 𝔛 O ρO κ toκ hϖ H) (hoRes 𝔛 O ρO κ toκ hϖ H) n yn
      (fun d => hy n d) hmem
  · rw [← hz]
    exact hoff _ (MvPolynomial.CrossingQuotient.Resolution.ι_apply_mem_offOrigins_of_not ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n) horig)

private scoped instance ρσ_lfp (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) : LocallyOfFinitePresentation ((C 𝔛 O ρO κ toκ hϖ H).ρ n ≫ (C 𝔛 O ρO κ toκ hϖ H).σ n) := by

  change LocallyOfFinitePresentation (MvPolynomial.CrossingQuotient.Resolution.toSpec ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n))
  haveI : IsProper (MvPolynomial.CrossingQuotient.Resolution.toCrossing ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)) :=
    MvPolynomial.CrossingQuotient.Resolution.isProper_toCrossing ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap O (MvPolynomial.CrossingQuotient O (((q : ℕ) : O) ^ (C 𝔛 O ρO κ toκ hϖ H).thick n))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  haveI : LocallyOfFiniteType (MvPolynomial.CrossingQuotient.Resolution.toSpec ((q : ℕ) : O) ((C 𝔛 O ρO κ toκ hϖ H).thick n)) := by
    delta MvPolynomial.CrossingQuotient.Resolution.toSpec
    infer_instance
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_isNoetherianRing _

private theorem mem_smoothOffEdges :
    ∀ y : 𝕐, (∀ (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (d : Fin (𝕎 n)), y ≠ edgePt 𝔛 O ρO κ toκ hϖ H n d) →
    y ∈ smoothOffEdges 𝔛 O ρO κ toκ hϖ H := by
  intro y hy
  rcases (D 𝔛 O ρO κ toκ hϖ H).ι_jointly_surjective y with ⟨x0, rfl⟩ | ⟨n, yn, rfl⟩
  · exact mem_smoothOffEdges_X0 𝔛 O ρO κ toκ hϖ H x0
  · have hgsm : Smooth ((C 𝔛 O ρO κ toκ hϖ H).g n) := by

      haveI := etale_f' 𝔛 O ρO κ toκ hϖ H n
      haveI : Smooth ((C 𝔛 O ρO κ toκ hϖ H).f n) := inferInstance
      exact MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
    have fac : (D 𝔛 O ρO κ toκ hϖ H).ιY n ≫ toBase 𝔛 O ρO κ toκ hϖ H =
        (C 𝔛 O ρO κ toκ hϖ H).g n ≫ ((C 𝔛 O ρO κ toκ hϖ H).ρ n ≫ (C 𝔛 O ρO κ toκ hϖ H).σ n) :=
      (C 𝔛 O ρO κ toκ hϖ H).ιY_toDR_πX n
    haveI hρσ : LocallyOfFinitePresentation ((C 𝔛 O ρO κ toκ hϖ H).ρ n ≫ (C 𝔛 O ρO κ toκ hϖ H).σ n) := ρσ_lfp 𝔛 O ρO κ toκ hϖ H n
    have hι : IsOpenImmersion ((D 𝔛 O ρO κ toκ hϖ H).ιY n) := by
      show IsOpenImmersion ((C 𝔛 O ρO κ toκ hϖ H).toGlueInput.ιY n)
      infer_instance
    exact Scheme.Hom.mem_smoothLocus_of_fac' (toBase 𝔛 O ρO κ toκ hϖ H) inferInstance ((D 𝔛 O ρO κ toκ hϖ H).ιY n) hι
      ((C 𝔛 O ρO κ toκ hϖ H).g n) ((C 𝔛 O ρO κ toκ hϖ H).ρ n ≫ (C 𝔛 O ρO κ toκ hϖ H).σ n) hgsm (ρσ_lfp 𝔛 O ρO κ toκ hϖ H n) fac yn
      (g_mem_smoothLocus_of_ne_edgePt 𝔛 O ρO κ toκ hϖ H n yn hy)

end V3AsmLevel
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry P2MW.S_V3AsmLevel_exists_smoothOffEdges.V3AsmLevel"

end
p2m_reactivate "P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial P2MW.S_V3AsmLevel_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3AsmLevel_exists_smoothOffEdges.AlgebraicGeometry P2MW.S_V3AsmLevel_exists_smoothOffEdges.V3AsmLevel"

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) :
    ∃ Wo : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H).Opens, SmoothOfRelativeDimension 1 (Wo.ι ≫ (V3AsmLevel.toBase 𝔛 O ρO κ toκ hϖ H)) ∧
      ∀ y : (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H), (∀ (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (d : Fin ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n)), y ≠ V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d) → y ∈ Wo :=
  ⟨V3AsmLevel.smoothOffEdges 𝔛 O ρO κ toκ hϖ H, V3AsmLevel.smoothOffEdges_smooth 𝔛 O ρO κ toκ hϖ H, V3AsmLevel.mem_smoothOffEdges 𝔛 O ρO κ toκ hϖ H⟩

end S_V3AsmLevel_exists_smoothOffEdges
end P2MW
export P2MW.S_V3AsmLevel_exists_smoothOffEdges (solution)
