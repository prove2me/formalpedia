-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierIntegralClosure_adjoin_root_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:49:51.400831+00:00
-- url     : https://prove2.me/submissions/1e602dcf-52f4-49a4-aa8b-7b1aa981dbee

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem quadraticArtinSchreierReciprocalPolynomial_aeval_root
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Polynomial.aeval (quadraticArtinSchreierReciprocalRoot P a ha)
        (quadraticArtinSchreierReciprocalPolynomial P a ha) = 0 := by
  rw [Polynomial.aeval_def]
  change eval₂
      ((AdjoinRoot.of (quadraticArtinSchreierPolynomial P a ha)).comp
        (algebraMap P.valuationRing K))
      (quadraticArtinSchreierReciprocalRoot P a ha)
      (quadraticArtinSchreierReciprocalPolynomial P a ha) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (quadraticArtinSchreierPolynomial P a ha)
private theorem quadraticArtinSchreier_minpoly_reciprocalRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    minpoly P.valuationRing (quadraticArtinSchreierReciprocalRoot P a ha) =
      quadraticArtinSchreierReciprocalPolynomial P a ha := by
  symm
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree P.valuationRing
      (QuadraticArtinSchreierField P a ha) :=
    Module.IsTorsionFree.trans_faithfulSMul P.valuationRing K
      (QuadraticArtinSchreierField P a ha)
  have hw_integral : IsIntegral P.valuationRing
      (quadraticArtinSchreierReciprocalRoot P a ha) := by
    have hport := (quadraticArtinSchreierIntegralRoot P a ha).property
    simp only [coe_quadraticArtinSchreierIntegralRoot] at hport ⊢
    exact hport
  have hmin_K : minpoly K (quadraticArtinSchreierReciprocalRoot P a ha) =
      quadraticArtinSchreierPolynomial P a ha := by
    simpa only [quadraticArtinSchreierReciprocalRoot,
      AdjoinRoot.powerBasis_gen] using
      AdjoinRoot.minpoly_powerBasis_gen_of_monic
        (quadraticArtinSchreierPolynomial_monic P a ha)
  have hmin_natDegree :
      (minpoly P.valuationRing
        (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree = 2 := by
    calc
      (minpoly P.valuationRing
          (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree =
          ((minpoly P.valuationRing
            (quadraticArtinSchreierReciprocalRoot P a ha)).map
              (algebraMap P.valuationRing K)).natDegree :=
        ((minpoly.monic hw_integral).natDegree_map _).symm
      _ = (minpoly K
          (quadraticArtinSchreierReciprocalRoot P a ha)).natDegree := by
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hw_integral]
      _ = (quadraticArtinSchreierPolynomial P a ha).natDegree := by
        rw [hmin_K]
      _ = 2 := quadraticArtinSchreierPolynomial_natDegree P a ha
  apply minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  · exact quadraticArtinSchreierReciprocalPolynomial_monic P a ha
  · exact quadraticArtinSchreierReciprocalPolynomial_aeval_root P a ha
  · rw [degree_eq_natDegree
        (quadraticArtinSchreierReciprocalPolynomial_monic P a ha).ne_zero,
      degree_eq_natDegree (minpoly.ne_zero hw_integral),
      quadraticArtinSchreierReciprocalPolynomial_natDegree, hmin_natDegree]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    Algebra.adjoin P.valuationRing
        ({quadraticArtinSchreierIntegralRoot P a ha} :
          Set (QuadraticArtinSchreierIntegralClosure P a ha)) = ⊤ := by
  let O := P.valuationRing
  let L := QuadraticArtinSchreierField P a ha
  let C := QuadraticArtinSchreierIntegralClosure P a ha
  let t : O := reciprocalUniformizer P a ha
  let w : C := quadraticArtinSchreierIntegralRoot P a ha
  let B : PowerBasis K L :=
    AdjoinRoot.powerBasis
      (quadraticArtinSchreierPolynomial_monic P a ha).ne_zero
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  have ht_irreducible : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr (by
      simpa only [O, t] using
        maximalIdeal_eq_span_reciprocalUniformizer P a ha)
  have hB_integral : IsIntegral O B.gen := by
    have hport := (quadraticArtinSchreierIntegralRoot P a ha).property
    simp only [O, B, AdjoinRoot.powerBasis_gen,
      coe_quadraticArtinSchreierIntegralRoot] at hport ⊢
    exact hport
  apply top_unique
  intro z _
  have hz_integral : IsIntegral O (z : L) := z.property
  have hcleared := Algebra.discr_mul_isIntegral_mem_adjoin K
    hB_integral hz_integral
  have hdisc_integral : IsIntegral O (Algebra.discr K B.basis) := by
    apply Algebra.discr_isIntegral K
    intro i
    rw [B.basis_eq_pow]
    exact hB_integral.pow _
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdisc_integral
  have hdisc_ne_zero : Algebra.discr K B.basis ≠ 0 :=
    (Algebra.discr_isUnit_of_basis K B.basis).ne_zero
  have hb_ne_zero : b ≠ 0 := by
    intro hb_zero
    apply hdisc_ne_zero
    rw [← hb, hb_zero, map_zero]
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb_ne_zero ht_irreducible
  rw [← hb, IsScalarTower.algebraMap_smul, hu] at hcleared
  have hcleared' := Subalgebra.smul_mem
    (Algebra.adjoin O ({B.gen} : Set L)) hcleared (↑(u⁻¹) : O)
  have ht_power : t ^ n • (z : L) ∈ Algebra.adjoin O ({B.gen} : Set L) := by
    simpa only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] using hcleared'
  have hminpoly_eisenstein :
      (minpoly O B.gen).IsEisensteinAt (Ideal.span ({t} : Set O)) := by
    have hE := quadraticArtinSchreierReciprocalPolynomial_isEisenstein P a ha
    rw [maximalIdeal_eq_span_reciprocalUniformizer P a ha] at hE
    have hminB : minpoly O B.gen =
        quadraticArtinSchreierReciprocalPolynomial P a ha := by
      have hport := quadraticArtinSchreier_minpoly_reciprocalRoot P a ha
      simp only [O, B, AdjoinRoot.powerBasis_gen] at hport ⊢
      exact hport
    rw [hminB]
    simpa only [O, t] using hE
  have hz_adjoin : (z : L) ∈ Algebra.adjoin O ({B.gen} : Set L) :=
    mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
      (B := B) (irreducible_iff_prime.mp ht_irreducible) hB_integral
      hz_integral ht_power hminpoly_eisenstein
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz_adjoin
  obtain ⟨q, hq⟩ := hz_adjoin
  have hq_mem : Polynomial.aeval w q ∈ Algebra.adjoin O ({w} : Set C) :=
    Polynomial.aeval_mem_adjoin_singleton O w
  have hq_eq : Polynomial.aeval w q = z := by
    apply Subtype.ext
    have hmap := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom O C L) w q
    change (IsScalarTower.toAlgHom O C L) (Polynomial.aeval w q) = (z : L)
    rw [← hmap]
    simp only [O, L, C, w, B,
      coe_quadraticArtinSchreierIntegralRoot,
      AdjoinRoot.powerBasis_gen] at hq ⊢
    exact hq
  rw [← hq_eq]
  exact hq_mem
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
