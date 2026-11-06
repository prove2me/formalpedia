-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.dvrParameterLocalFibre_isField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:57:40.852135+00:00
-- url     : https://prove2.me/submissions/3008e33f-f359-4885-8155-24bbec4a3f7e

import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvrParameterLocalMap_mapMaximal

set_option autoImplicit false
open scoped TensorProduct
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)
attribute [local instance] QEC.Coding.AlgebraicGeometry.dvrParameterPrime_isPrime
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsDiscreteValuationRing V] (hπ : Irreducible π) :
    let R := Localization.AtPrime (dvrParameterPrime k V π)
    letI : Algebra R V :=
      (dvrParameterLocalMap k V π).toRingHom.toAlgebra
    IsField (IsLocalRing.ResidueField R ⊗[R] V) := by
  let R := Localization.AtPrime (dvrParameterPrime k V π)
  let : Algebra R V :=
    (dvrParameterLocalMap k V π).toRingHom.toAlgebra
  have hm : Ideal.map (algebraMap R V) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal V :=
    dvrParameterLocalMap_mapMaximal k V π hπ
  let e : (IsLocalRing.ResidueField R ⊗[R] V) ≃+* IsLocalRing.ResidueField V :=
    (Algebra.TensorProduct.comm R (IsLocalRing.ResidueField R) V).toRingEquiv.trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot V
        (IsLocalRing.maximalIdeal R)).symm.toRingEquiv.trans
          (Ideal.quotientEquivAlgOfEq V hm).toRingEquiv)
  exact e.isField (Field.toIsField (IsLocalRing.ResidueField V))
end QEC.Coding.AlgebraicGeometry
