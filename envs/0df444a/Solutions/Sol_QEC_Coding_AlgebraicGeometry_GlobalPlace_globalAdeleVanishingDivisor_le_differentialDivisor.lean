-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleVanishingDivisor_le_differentialDivisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:52:40.030205+00:00
-- url     : https://prove2.me/submissions/557cf316-75ac-414a-9971-d497d1e82ecb

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_differentialDivisor_mem_globalAdeleVanishingDivisors
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleSmulIntoDifferentialSpace_coe
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
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


section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] globalAdeleDifferentialWeilAlgebra
attribute [local instance] globalAdeleDifferentialWeilScalarTower
namespace GlobalPlace
variable [IsFullConstantField k F]
private theorem globalAdeleFilter_sup_eq_add
    {D₁ D₂ : Divisor (GlobalPlace k F)} :
    globalAdeleFilter (k := k) (F := F) (D₁ ⊔ D₂) =
      globalAdeleFilter (k := k) (F := F) D₁ +
        globalAdeleFilter (k := k) (F := F) D₂ := by
  classical
  rw [Submodule.add_eq_sup]
  apply le_antisymm
  · intro a ha
    have haevent := a.property
    change ∀ᶠ P : GlobalPlace k F in Filter.cofinite,
      a.val P ∈ P.valuationRing at haevent
    let a₁ : GlobalAdele (k := k) (F := F) :=
      ⟨fun P => if D₂ P ≤ D₁ P then a.val P else 0, by
        change ∀ᶠ P : GlobalPlace k F in Filter.cofinite,
          (if D₂ P ≤ D₁ P then a.val P else 0) ∈ P.valuationRing
        exact haevent.mono fun P hP => by
          by_cases h : D₂ P ≤ D₁ P
          · rw [if_pos h]
            exact hP
          · rw [if_neg h]
            exact P.valuationRing.zero_mem⟩
    let a₂ : GlobalAdele (k := k) (F := F) :=
      ⟨fun P => if D₂ P ≤ D₁ P then 0 else a.val P, by
        change ∀ᶠ P : GlobalPlace k F in Filter.cofinite,
          (if D₂ P ≤ D₁ P then 0 else a.val P) ∈ P.valuationRing
        exact haevent.mono fun P hP => by
          by_cases h : D₂ P ≤ D₁ P
          · rw [if_pos h]
            exact P.valuationRing.zero_mem
          · rw [if_neg h]
            exact hP⟩
    have ha₁ : a₁ ∈ globalAdeleFilter (k := k) (F := F) D₁ := by
      intro P
      by_cases h : D₂ P ≤ D₁ P
      · change P.valuation (if D₂ P ≤ D₁ P then a.val P else 0) ≤ _
        rw [if_pos h]
        simpa only [Finsupp.sup_apply, sup_eq_left.mpr h] using ha P
      · simp only [a₁, if_neg h, map_zero]
        exact zero_le
    have ha₂ : a₂ ∈ globalAdeleFilter (k := k) (F := F) D₂ := by
      intro P
      by_cases h : D₂ P ≤ D₁ P
      · simp only [a₂, if_pos h, map_zero]
        exact zero_le
      · have hle : D₁ P ≤ D₂ P := le_of_not_ge h
        change P.valuation (if D₂ P ≤ D₁ P then 0 else a.val P) ≤ _
        rw [if_neg h]
        simpa only [Finsupp.sup_apply, sup_eq_right.mpr hle] using ha P
    refine Submodule.mem_sup.mpr ⟨a₁, ha₁, a₂, ha₂, ?_⟩
    ext P
    by_cases h : D₂ P ≤ D₁ P <;> simp [a₁, a₂, h]
  · apply sup_le
    · exact globalAdeleFilter_mono (k := k) (F := F) le_sup_left
    · exact globalAdeleFilter_mono (k := k) (F := F) le_sup_right
private theorem globalAdeleVanishingDivisors_sup
    {omega : GlobalAdeleWeilDifferential k F}
    {D₁ D₂ : Divisor (GlobalPlace k F)}
    (hD₁ : D₁ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega)
    (hD₂ : D₂ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega) :
    D₁ ⊔ D₂ ∈ globalAdeleVanishingDivisors (k := k) (F := F) omega := by
  intro a ha
  change a ∈ globalAdeleFilter (k := k) (F := F) (D₁ ⊔ D₂) +
      diagonalAdeleSubmodule (k := k) (F := F) at ha
  rw [globalAdeleFilter_sup_eq_add] at ha
  rcases Submodule.mem_sup.mp ha with ⟨b, hb, d, hd, rfl⟩
  rcases Submodule.mem_sup.mp hb with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
  have hsplit : a₁ + a₂ + d = (a₁ + d) + a₂ := by abel
  rw [hsplit, map_add]
  have hleft : omega.toFun (a₁ + d) = 0 := by
    apply hD₁
    exact Submodule.mem_sup.mpr ⟨a₁, ha₁, d, hd, rfl⟩
  have hright : omega.toFun a₂ = 0 := by
    apply hD₂
    exact Submodule.mem_sup_left ha₂
  rw [hleft, hright, add_zero]
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialWeilAlgebra
attribute [local instance] globalAdeleDifferentialWeilAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialWeilScalarTower
attribute [local instance] globalAdeleDifferentialWeilScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (omega : Differential k F) (homega : omega ≠ 0)
    {D : Divisor (GlobalPlace k F)}
    (hD : D ∈ globalAdeleVanishingDivisors (k := k) (F := F)
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega)) :
    D ≤ FunctionFieldDifferential.differentialDivisor
      (k := k) (F := F) omega homega := by
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  intro P
  by_contra hnot
  have hstrict : K P < D P := lt_of_not_ge hnot
  have hsup : K ⊔ D ∈ globalAdeleVanishingDivisors (k := k) (F := F)
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega) :=
    globalAdeleVanishingDivisors_sup
      (k := k) (F := F)
      (differentialDivisor_mem_globalAdeleVanishingDivisors
        (k := k) (F := F) omega homega) hD
  have hle : K + placeDivisor P ≤ K ⊔ D := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      simp only [Finsupp.add_apply, placeDivisor_apply, Finsupp.sup_apply]
      omega
    · simp only [Finsupp.add_apply,
        placeDivisor_apply_of_ne P Q (Ne.symm hQP), add_zero,
        Finsupp.sup_apply]
      exact le_sup_left
  obtain ⟨a, ha⟩ :=
    globalAdeleSimplePoleResidueSum_filter_add_placeDivisor_surjective
      (k := k) (F := F) omega homega P (1 : k)
  have hvanish :
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega).toFun
          (a : GlobalAdele (k := k) (F := F)) = 0 := by
    apply hsup
    exact Submodule.mem_sup_left
      (globalAdeleFilter_mono (k := k) (F := F) hle a.property)
  have hvalue :
      (globalAdeleWeilDifferentialOfDifferential
        (k := k) (F := F) omega homega).toFun
          (a : GlobalAdele (k := k) (F := F)) = 1 := by
    rw [globalAdeleWeilDifferentialOfDifferential_toFun_of_mem_simplePole
      (k := k) (F := F) omega homega _
      (globalAdeleFilter_add_placeDivisor_le_globalAdeleSimplePoleSubmodule
        (k := k) (F := F) omega homega P a.property)]
    exact ha
  exact one_ne_zero (hvalue.symm.trans hvanish)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
