-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepIntegralClosure_adjoin_root_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:50:18.642911+00:00
-- url     : https://prove2.me/submissions/eb29870e-a3b1-40b9-a418-8b968e9b6aae

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem sourceStepReciprocalPolynomial_aeval_sourceStepReciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Polynomial.aeval (sourceStepReciprocalRoot P x hx)
        (sourceStepReciprocalPolynomial P x hx) = 0 := by
  rw [Polynomial.aeval_def]
  change eval₂
      ((AdjoinRoot.of (sourceStepPolynomial P x hx)).comp
        (algebraMap P.valuationRing K))
      (sourceStepReciprocalRoot P x hx)
      (sourceStepReciprocalPolynomial P x hx) = 0
  rw [← eval₂_map]
  exact AdjoinRoot.eval₂_root (sourceStepPolynomial P x hx)
private theorem sourceStep_minpoly_reciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    minpoly P.valuationRing (sourceStepReciprocalRoot P x hx) =
      sourceStepReciprocalPolynomial P x hx := by
  symm
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree P.valuationRing (SourceStepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      P.valuationRing K (SourceStepField P x hx)
  have hw_integral : IsIntegral P.valuationRing
      (sourceStepReciprocalRoot P x hx) := by
    have hport := (sourceStepIntegralRoot P x hx).property
    simp only [coe_sourceStepIntegralRoot] at hport ⊢
    exact hport
  have hmin_K : minpoly K (sourceStepReciprocalRoot P x hx) =
      sourceStepPolynomial P x hx := by
    simpa only [sourceStepReciprocalRoot, AdjoinRoot.powerBasis_gen] using
      AdjoinRoot.minpoly_powerBasis_gen_of_monic
        (sourceStepPolynomial_monic P x hx)
  have hmin_natDegree :
      (minpoly P.valuationRing
        (sourceStepReciprocalRoot P x hx)).natDegree = 16 := by
    calc
      (minpoly P.valuationRing
          (sourceStepReciprocalRoot P x hx)).natDegree =
          ((minpoly P.valuationRing
            (sourceStepReciprocalRoot P x hx)).map
              (algebraMap P.valuationRing K)).natDegree :=
        ((minpoly.monic hw_integral).natDegree_map _).symm
      _ = (minpoly K (sourceStepReciprocalRoot P x hx)).natDegree := by
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hw_integral]
      _ = (sourceStepPolynomial P x hx).natDegree := by rw [hmin_K]
      _ = 16 := sourceStepPolynomial_natDegree P x hx
  apply minpoly.IsIntegrallyClosed.unique_of_degree_le_degree_minpoly
  · exact sourceStepReciprocalPolynomial_monic P x hx
  · exact sourceStepReciprocalPolynomial_aeval_sourceStepReciprocalRoot P x hx
  · rw [degree_eq_natDegree
        (sourceStepReciprocalPolynomial_monic P x hx).ne_zero,
      degree_eq_natDegree (minpoly.ne_zero hw_integral),
      sourceStepReciprocalPolynomial_natDegree, hmin_natDegree]
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
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    Algebra.adjoin P.valuationRing
        ({sourceStepIntegralRoot P x hx} :
          Set (SourceStepIntegralClosure P x hx)) = ⊤ := by
  let O := P.valuationRing
  let L := SourceStepField P x hx
  let C := SourceStepIntegralClosure P x hx
  let t : O := sourceStepUniformizer P x hx
  let w : C := sourceStepIntegralRoot P x hx
  let B : PowerBasis K L :=
    AdjoinRoot.powerBasis (sourceStepPolynomial_monic P x hx).ne_zero
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  have ht_irreducible : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr (by
      simpa only [O, t, sourceStepUniformizer] using
        maximalIdeal_eq_span_reciprocalUniformizer P
          (sourceStepRhs x) (sourceStepRhs_order P x hx))
  have hB_integral : IsIntegral O B.gen := by
    have hport := (sourceStepIntegralRoot P x hx).property
    simp only [O, B, AdjoinRoot.powerBasis_gen, coe_sourceStepIntegralRoot] at hport ⊢
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
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdisc_integral
  have hdisc_ne_zero : Algebra.discr K B.basis ≠ 0 :=
    (Algebra.discr_isUnit_of_basis K B.basis).ne_zero
  have ha_ne_zero : a ≠ 0 := by
    intro ha_zero
    apply hdisc_ne_zero
    rw [← ha, ha_zero, map_zero]
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha_ne_zero ht_irreducible
  rw [← ha, IsScalarTower.algebraMap_smul, hu] at hcleared
  have hcleared' := Subalgebra.smul_mem
    (Algebra.adjoin O ({B.gen} : Set L)) hcleared (↑(u⁻¹) : O)
  have ht_power : t ^ n • (z : L) ∈ Algebra.adjoin O ({B.gen} : Set L) := by
    simpa only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] using hcleared'
  have hminpoly_eisenstein :
      (minpoly O B.gen).IsEisensteinAt (Ideal.span ({t} : Set O)) := by
    have hE := sourceStepReciprocalPolynomial_isEisenstein P x hx
    rw [maximalIdeal_eq_span_reciprocalUniformizer P
      (sourceStepRhs x) (sourceStepRhs_order P x hx)] at hE
    have hminB : minpoly O B.gen = sourceStepReciprocalPolynomial P x hx := by
      have hport := sourceStep_minpoly_reciprocalRoot P x hx
      simp only [O, B, AdjoinRoot.powerBasis_gen] at hport ⊢
      exact hport
    rw [hminB]
    simpa only [O, t, sourceStepUniformizer] using hE
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
    have hport := hq
    simp only [O, L, C, w, B, coe_sourceStepIntegralRoot, AdjoinRoot.powerBasis_gen] at hport ⊢
    exact hport
  rw [← hq_eq]
  exact hq_mem
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
