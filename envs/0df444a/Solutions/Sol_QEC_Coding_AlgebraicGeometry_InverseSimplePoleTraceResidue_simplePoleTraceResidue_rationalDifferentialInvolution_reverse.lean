-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.simplePoleTraceResidue_rationalDifferentialInvolution_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:53:19.377558+00:00
-- url     : https://prove2.me/submissions/25f87c4d-4f0f-43da-87a1-7ab920d11074

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_SimplePoleTraceResidue
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_Nonnegative_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferential_eq_coordinate_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_simplePoleTraceResidue_rationalDifferentialInvolution
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
namespace QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
open scoped Polynomial RatFunc BigOperators
open FunctionFieldDifferential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k] [Finite k]
omit [Finite k] in
private theorem rationalInvolution_involutive (f : RatFunc k) :
    InverseAffinePlace.rationalInvolution k
      (InverseAffinePlace.rationalInvolution k f) = f := by
  let e := InverseAffinePlace.rationalInvolution k
  have hhom : e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom =
      RingHom.id (RatFunc k) := by
    apply IsFractionRing.ringHom_ext (A := k[X])
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simpa only [RingHom.comp_apply, RingHom.id_apply, map_add] using
          congrArg₂ (fun x y => x + y) hp hq
    | monomial n a =>
        have hC : e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) =
            (algebraMap k[X] (RatFunc k)) (Polynomial.C a) := by
          change e (e (algebraMap k (RatFunc k) a)) =
            algebraMap k (RatFunc k) a
          rw [e.commutes, e.commutes]
        have hX : e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) =
            (algebraMap k[X] (RatFunc k)) Polynomial.X := by
          change e (e RatFunc.X) = RatFunc.X
          rw [InverseAffinePlace.rationalInvolution_X, map_inv₀,
            InverseAffinePlace.rationalInvolution_X, inv_inv]
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp only [RingHom.comp_apply, RingHom.id_apply, map_mul, map_pow]
        change e (e ((algebraMap k[X] (RatFunc k)) (Polynomial.C a))) *
            e (e ((algebraMap k[X] (RatFunc k)) Polynomial.X)) ^ n =
          (algebraMap k[X] (RatFunc k)) (Polynomial.C a) *
            (algebraMap k[X] (RatFunc k)) Polynomial.X ^ n
        rw [hC, hX]
  change (e.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom) f = f
  rw [hhom]
  rfl
omit [Finite k] in
private theorem rationalDifferentialInvolution_logarithmicDifferential
    (f : RatFunc k) :
    InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
        (Differential.logarithmicDifferential
          (k := k) (F := RatFunc k) f) =
      Differential.logarithmicDifferential (k := k) (F := RatFunc k)
        (InverseAffinePlace.rationalInvolution k f) := by
  rw [Differential.logarithmicDifferential,
    InverseRationalInfinityTransport.rationalDifferentialInvolution_smul,
    InverseRationalInfinityTransport.rationalDifferentialInvolution_differential,
    map_inv₀]
  rfl
omit [Finite k] in
private theorem rationalDifferentialInvolution_involutive
    (omega : Differential k (RatFunc k)) :
    InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
        (InverseRationalInfinityTransport.rationalDifferentialInvolution
          (k := k) omega) = omega := by
  let e := InverseAffinePlace.rationalInvolution k
  let C := functionFieldDifferentialCoordinate (k := k) (F := RatFunc k)
  let dX := functionFieldDifferentialGenerator (k := k) (F := RatFunc k)
  have homega : omega = C omega • dX :=
    functionFieldDifferential_eq_coordinate_smul_generator
      (k := k) (F := RatFunc k) omega
  calc
    InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
        (InverseRationalInfinityTransport.rationalDifferentialInvolution
          (k := k) omega) =
        InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
          (InverseRationalInfinityTransport.rationalDifferentialInvolution
            (k := k) (C omega • dX)) := by
              exact congrArg
                (InverseRationalInfinityTransport.rationalDifferentialInvolution
                  (k := k))
                (congrArg
                  (InverseRationalInfinityTransport.rationalDifferentialInvolution
                    (k := k)) homega)
    _ = InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
          (e (C omega) •
            InverseRationalInfinityTransport.rationalDifferentialInvolution
              (k := k) dX) := by
            rw [InverseRationalInfinityTransport.rationalDifferentialInvolution_smul]
    _ = e (e (C omega)) •
          InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
            (InverseRationalInfinityTransport.rationalDifferentialInvolution
              (k := k) dX) := by
            rw [InverseRationalInfinityTransport.rationalDifferentialInvolution_smul]
    _ = C omega • dX := by
      simp only [dX, functionFieldDifferentialGenerator]
      rw [InverseRationalInfinityTransport.rationalDifferentialInvolution_differential,
        InverseRationalInfinityTransport.rationalDifferentialInvolution_differential,
        rationalInvolution_involutive, rationalInvolution_involutive]
    _ = omega := homega.symm
section DirectFactor
variable {F : Type*} [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] infinityDirectConstantAlgebra
attribute [local instance] infinityDirectConstantScalarTower
end DirectFactor
section InfinityFibre
variable {F : Type*} [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra (RatFunc k) F]
variable [oldScalarTower : IsScalarTower k[X] (RatFunc k) F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] directConstantAlgebra
attribute [local instance] directConstantScalarTower
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inversePolynomialAlgebra" =>
  InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseScalarTower" =>
  InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F
end InfinityFibre
end QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
open scoped Polynomial RatFunc BigOperators
open FunctionFieldDifferential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
theorem _root_.solution
    (eta : Differential k (RatFunc k))
    (heta : eta ∈ Differential.simplePoleDifferentialLattice
      (InverseRationalInfinityTransport.xAdicPlace k)) :
    ∃ hback :
        InverseRationalInfinityTransport.rationalDifferentialInvolution
            (k := k) eta ∈
          Differential.simplePoleDifferentialLattice
            (GlobalPlace.rationalInfinity k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k)
          (InverseRationalInfinityTransport.rationalDifferentialInvolution
            (k := k) eta) hback =
        Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (InverseRationalInfinityTransport.xAdicPlace k) eta heta := by
  let P := GlobalPlace.rationalInfinity k
  let Q := GlobalPlace.rationalAdic (Polynomial.idealX k)
  let e := InverseAffinePlace.rationalInvolution k
  let pi : Q.valuationRing := Q.uniformizerInValuationRing
  let r : Q.valuationRing :=
    Differential.simplePoleResidueCoordinate (k := k) (F := RatFunc k) Q
      ⟨eta, heta⟩
  let f : RatFunc k := e (pi : RatFunc k)
  have hpi : (pi : RatFunc k) ≠ 0 := by
    change Q.uniformizer ≠ 0
    exact Differential.localParameter_ne_zero (k := k) (F := RatFunc k) Q
  have hf : f ≠ 0 :=
    (map_ne_zero_iff _ e.injective).mpr hpi
  let rback : P.valuationRing := ⟨e (r : RatFunc k), by
    rw [GlobalPlace.mem_valuationRing_iff]
    have hvalue :=
      InverseRationalInfinityTransport.xAdic_valuation_rationalInvolution_eq_rationalInfinity_valuation
        (k := k) (e (r : RatFunc k))
    rw [rationalInvolution_involutive] at hvalue
    rw [← hvalue]
    exact r.property⟩
  have hetaDecomposition :
      eta = (r : RatFunc k) •
        Differential.logarithmicDifferential (k := k) (F := RatFunc k)
          (pi : RatFunc k) := by
    exact Differential.simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
      (k := k) (F := RatFunc k) Q ⟨eta, heta⟩
  let logAt : Differential.simplePoleDifferentialLattice P :=
    Differential.logarithmicDifferentialAtSimplePole
      (k := k) (F := RatFunc k) P f hf
  have hbackDecomposition :
      InverseRationalInfinityTransport.rationalDifferentialInvolution
          (k := k) eta =
        ((rback : P.valuationRing) : RatFunc k) •
          (logAt : Differential k (RatFunc k)) := by
    calc
      InverseRationalInfinityTransport.rationalDifferentialInvolution
          (k := k) eta =
          InverseRationalInfinityTransport.rationalDifferentialInvolution
            (k := k)
            ((r : RatFunc k) •
              Differential.logarithmicDifferential
                (k := k) (F := RatFunc k) (pi : RatFunc k)) := by
                  rw [hetaDecomposition]
      _ = e (r : RatFunc k) •
          InverseRationalInfinityTransport.rationalDifferentialInvolution
            (k := k)
            (Differential.logarithmicDifferential
              (k := k) (F := RatFunc k) (pi : RatFunc k)) := by
                rw [InverseRationalInfinityTransport.rationalDifferentialInvolution_smul]
      _ = ((rback : P.valuationRing) : RatFunc k) •
          (logAt : Differential k (RatFunc k)) := by
            rw [rationalDifferentialInvolution_logarithmicDifferential]
            rfl
  have hback :
      InverseRationalInfinityTransport.rationalDifferentialInvolution
          (k := k) eta ∈
        Differential.simplePoleDifferentialLattice P := by
    rw [hbackDecomposition]
    exact (Differential.simplePoleDifferentialLattice P).smul_mem
      rback logAt.property
  obtain ⟨hforward, hresidue⟩ :=
    InverseRationalInfinityTransport.simplePoleTraceResidue_rationalDifferentialInvolution
      (k := k)
      (InverseRationalInfinityTransport.rationalDifferentialInvolution
        (k := k) eta) hback
  refine ⟨hback, ?_⟩
  have hinvolutive := rationalDifferentialInvolution_involutive (k := k) eta
  simpa only [P, Q, hinvolutive] using hresidue.symm
end QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
