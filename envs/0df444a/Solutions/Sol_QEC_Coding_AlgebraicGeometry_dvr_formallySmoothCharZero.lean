-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvr_formallySmoothCharZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:59:42.262237+00:00
-- url     : https://prove2.me/submissions/026b4527-d0d2-4874-b10b-a10e4b6e5813

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalMap_flat
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalMap_isLocalHom
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalFibre_isField

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [CharZero k] [IsDiscreteValuationRing V] [Algebra.EssFiniteType k V] :
    Algebra.FormallySmooth k V := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let R := Localization.AtPrime (dvrParameterPrime k V π)
  let φ := dvrParameterLocalMap k V π
  let : Algebra R V := φ.toRingHom.toAlgebra
  let : SMul k R := Algebra.toSMul
  let : Module k R := Algebra.toModule
  let : SMul k V := Algebra.toSMul
  let : Module k V := Algebra.toModule
  let : SMul R V := Algebra.toSMul
  let : Module R V := Algebra.toModule
  let : IsScalarTower k R V := .of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Module.Flat R V := RingHom.flat_algebraMap_iff.mp
    (dvrParameterLocalMap_flat k V π hπ)
  let : IsLocalHom (algebraMap R V) :=
    dvrParameterLocalMap_isLocalHom k V π
  let : Algebra.EssFiniteType R V := .of_comp k R V
  let P := Algebra.EssFiniteType.subalgebra R V
  let M := Algebra.EssFiniteType.submonoid R V
  let : Algebra.FinitePresentation R P :=
    (Algebra.FinitePresentation.of_finiteType (R := R) (A := P)).mp inferInstance
  let F := IsLocalRing.ResidueField R ⊗[R] V
  let : Field F := (dvrParameterLocalFibre_isField k V π hπ).toField
  let : CharZero (IsLocalRing.ResidueField R) :=
    charZero_of_injective_algebraMap (algebraMap k (IsLocalRing.ResidueField R)).injective
  let : PerfectField (IsLocalRing.ResidueField R) := inferInstance
  let : Algebra.FormallySmooth (IsLocalRing.ResidueField R) F :=
    Algebra.FormallySmooth.of_perfectField
  let : Algebra.FormallySmooth R V :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := R) (S := V) (P := P) M
  let : Algebra.FormallySmooth (Polynomial k) R :=
    Algebra.FormallySmooth.of_isLocalization
      (dvrParameterPrime k V π).primeCompl
  let : IsScalarTower k (Polynomial k) R := inferInstance
  let : Algebra.FormallySmooth k R := .comp k (Polynomial k) R
  exact Algebra.FormallySmooth.comp k R V
end QEC.Coding.AlgebraicGeometry
