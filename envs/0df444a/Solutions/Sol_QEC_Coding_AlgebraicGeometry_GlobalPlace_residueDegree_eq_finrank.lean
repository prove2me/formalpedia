-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:19.269897+00:00
-- url     : https://prove2.me/submissions/f47085cf-1c64-472a-8039-868f6894d989

import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_inverseFibre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_affine
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
section
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry
private theorem inverseFibreGlobalPlaceAt_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (κ : Algebra k F)
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D) =
      inverseFibreRawValuation D := rfl
private theorem affineResidueDegree_eq_globalResidueField_finrank
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) (C : AffinePlace.carrier k F)
    (hvaluation : P.valuation = C.valuation F) :
    letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
    letI : FiniteDimensional k (GlobalPlace.residueField P) :=
      GlobalPlace.residueField_finiteDimensional P
    AffinePlace.residueDegree k F C =
      Module.finrank k (GlobalPlace.residueField P) := by
  letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  letI : Algebra k (AffinePlace.residueField k F C) :=
    AffinePlace.residueAlgebra k F C
  letI : FiniteDimensional k (AffinePlace.residueField k F C) :=
    AffinePlace.residueField_finiteDimensional k F C
  let e₁ : Localization.AtPrime C.asIdeal ≃+*
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C :=
    (Localization.algEquiv C.asIdeal.primeCompl
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C)).toRingEquiv
  let e₂ : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F C ≃+*
      P.valuation.valuationSubring := by
    rw [C.valuationSubringAtPrime_eq_valuationSubring, hvaluation]
  let e : AffinePlace.residueField k F C ≃+* GlobalPlace.residueField P :=
    IsLocalRing.ResidueField.mapEquiv (e₁.trans e₂)
  unfold AffinePlace.residueDegree
  apply Nat.pow_right_injective (a := Nat.card k) (by
    letI : Fintype k := Fintype.ofFinite k
    simpa only [Nat.card_eq_fintype_card] using
      (Nat.succ_le_of_lt (Fintype.one_lt_card : 1 < Fintype.card k)))
  change Nat.card k ^ Module.finrank k (AffinePlace.residueField k F C) =
    Nat.card k ^ Module.finrank k (GlobalPlace.residueField P)
  rw [← Module.natCard_eq_pow_finrank (K := k)
      (V := AffinePlace.residueField k F C),
    ← Module.natCard_eq_pow_finrank (K := k)
      (V := GlobalPlace.residueField P)]
  exact Nat.card_congr e.toEquiv
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
    letI : FiniteDimensional k (GlobalPlace.residueField P) :=
      GlobalPlace.residueField_finiteDimensional P
    GlobalPlace.residueDegree P = Module.finrank k (GlobalPlace.residueField P) := by
  letI : Algebra k (GlobalPlace.residueField P) := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  let C := (chartGlobalPlaceEquiv (k := k) (F := F)).symm P
  have hP : chartGlobalPlaceEquiv (k := k) (F := F) C = P :=
    (chartGlobalPlaceEquiv (k := k) (F := F)).apply_symm_apply P
  rcases C with C | D
  · have hvaluation : P.valuation = C.valuation F := by
      rw [← hP, chartGlobalPlaceEquiv_apply]
      rfl
    rw [GlobalPlace.residueDegree_eq_affine P C hvaluation]
    exact affineResidueDegree_eq_globalResidueField_finrank P C hvaluation
  · have hvaluationRaw : P.valuation =
        inverseFibreRawValuation
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D := by
      rw [← hP, chartGlobalPlaceEquiv_apply]
      rfl
    have hvaluationGlobal : P.valuation =
        @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D) :=
      hvaluationRaw.trans
        (inverseFibreGlobalPlaceAt_valuation
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D).symm
    rw [GlobalPlace.residueDegree_eq_inverseFibre P D hvaluationGlobal]
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    have hvaluationAffine : P.valuation = D.1.valuation F :=
      hvaluationRaw.trans
        (inverseFibreRawValuation_eq_ambient
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D)
    change AffinePlace.residueDegree k F D.1 =
      Module.finrank k (GlobalPlace.residueField P)
    exact affineResidueDegree_eq_globalResidueField_finrank P D.1 hvaluationAffine
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
