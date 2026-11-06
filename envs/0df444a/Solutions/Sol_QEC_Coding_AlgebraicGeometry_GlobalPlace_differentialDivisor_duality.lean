-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.differentialDivisor_duality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:56:14.274139+00:00
-- url     : https://prove2.me/submissions/ad61530d-c4e9-4743-be9d-870f0960672c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_add_principal_mem_globalAdeleVanishingDivisors_smul_iff
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_differentialDivisor_mem_globalAdeleVanishingDivisors
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleVanishingDivisor_le_differentialDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleWeilDifferentialOfDifferential_isNonzero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleWeilDifferential_finrank_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSmulIntoDifferentialSpace_coe
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialDualityAlgebra
attribute [local instance] globalAdeleDifferentialDualityAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialDualityScalarTower
attribute [local instance] globalAdeleDifferentialDualityScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleDifferentialDualityRiemannRochFiniteDimensional
attribute [local instance] globalAdeleDifferentialDualityRiemannRochFiniteDimensional
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (omega : Differential k F) (homega : omega ≠ 0)
    (D : Divisor (GlobalPlace k F)) :
    riemannRochDimension
        (FunctionFieldDifferential.differentialDivisor
          (k := k) (F := F) omega homega - D) =
      riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D := by
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  let omegaA := globalAdeleWeilDifferentialOfDifferential
    (k := k) (F := F) omega homega
  have hKmem : K ∈ globalAdeleVanishingDivisors (k := k) (F := F) omegaA :=
    differentialDivisor_mem_globalAdeleVanishingDivisors
      (k := k) (F := F) omega homega
  have homegaAToFun : omegaA.toFun ≠ 0 :=
    globalAdeleWeilDifferentialOfDifferential_isNonzero
      (k := k) (F := F) omega homega
  have homegaA : omegaA ≠ 0 := by
    intro hzero
    apply homegaAToFun
    rw [hzero]
    rfl
  have hKD : K - (K - D) = D := sub_sub_cancel K D
  let mu := globalAdeleSmulIntoDifferentialSpace
    (k := k) (F := F) omegaA hKmem (K - D)
  have hmuInjective : Function.Injective mu :=
    globalAdeleSmulIntoDifferentialSpace_injective
      (k := k) (F := F) omegaA hKmem (K - D) homegaAToFun
  have hmuSurjective : Function.Surjective mu := by
    intro psi
    let eta : GlobalAdeleWeilDifferential k F :=
      ⟨(psi : GlobalAdele (k := k) (F := F) →ₗ[k] k), ⟨D, by
        intro a ha
        exact psi.property a (by simpa only [hKD] using ha)⟩⟩
    have hetaD : D ∈ globalAdeleVanishingDivisors (k := k) (F := F) eta := by
      intro a ha
      change (psi : GlobalAdele (k := k) (F := F) →ₗ[k] k) a = 0
      exact psi.property a (by simpa only [hKD] using ha)
    by_cases hpsi : (psi : GlobalAdele (k := k) (F := F) →ₗ[k] k) = 0
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simpa only [map_zero, Submodule.coe_zero] using hpsi.symm
    · have hetaToFun : eta.toFun ≠ 0 := hpsi
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
        (globalAdeleWeilDifferential_finrank_eq_one
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
        homegaA eta
      have hc0 : c ≠ 0 := by
        intro hcZero
        subst c
        apply hetaToFun
        have hetaZero : eta = 0 := by
          rw [← hc, zero_smul]
        rw [hetaZero]
        rfl
      let cu : Fˣ := Units.mk0 c hc0
      let J := principalDivisor (k := k) (F := F) cu
      have hDmem : D ∈ globalAdeleVanishingDivisors (k := k) (F := F)
          (GlobalAdeleWeilDifferential.smulWeil (cu : F) omegaA) := by
        have hscaled : GlobalAdeleWeilDifferential.smulWeil (cu : F) omegaA =
            eta := by
          exact hc
        rw [hscaled]
        exact hetaD
      have hDJmem : D - J ∈
          globalAdeleVanishingDivisors (k := k) (F := F) omegaA := by
        apply (add_principal_mem_globalAdeleVanishingDivisors_smul_iff
          (k := k) (F := F) cu omegaA (D - J)).mp
        simpa only [J, sub_add_cancel] using hDmem
      have hDJle : D - J ≤ K :=
        globalAdeleVanishingDivisor_le_differentialDivisor
          (k := k) (F := F) omega homega hDJmem
      have hcmem : c ∈ riemannRochSubmodule (K - D) := by
        apply (mem_riemannRochSubmodule_iff_order_add_nonnegative
          (K - D) hc0).mpr
        intro P
        have hP := hDJle P
        simp only [Finsupp.sub_apply, J, principalDivisor_apply,
          cu, Units.val_mk0] at hP ⊢
        omega
      refine ⟨⟨c, hcmem⟩, ?_⟩
      apply Subtype.ext
      rw [globalAdeleSmulIntoDifferentialSpace_coe]
      change (GlobalAdeleWeilDifferential.smulWeil c omegaA).toFun =
        (psi : GlobalAdele (k := k) (F := F) →ₗ[k] k)
      exact congrArg GlobalAdeleWeilDifferential.toFun hc
  let e := LinearEquiv.ofBijective mu ⟨hmuInjective, hmuSurjective⟩
  have hfinrank :
      Module.finrank k (riemannRochSubmodule (K - D)) =
        Module.finrank k
          (globalAdeleDifferentialSpace (k := k) (F := F) (K - (K - D))) :=
    e.finrank_eq
  change Module.finrank k (riemannRochSubmodule (K - D)) =
    riemannRochIndexOfSpecialty
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  rw [hfinrank, hKD,
    globalAdeleDifferentialSpace_finrank_eq_indexOfSpecialty]
end QEC.Coding.AlgebraicGeometry.GlobalPlace
