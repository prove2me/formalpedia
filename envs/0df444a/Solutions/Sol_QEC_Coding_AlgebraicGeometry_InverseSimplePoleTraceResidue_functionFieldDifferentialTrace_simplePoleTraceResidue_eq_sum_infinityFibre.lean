-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:03:47.773369+00:00
-- url     : https://prove2.me/submissions/2eb0ce21-a574-489b-8c28-46aa49b3c304

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_SimplePoleTraceResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseSimplePoleTraceResidue_simplePoleTraceResidue_rationalDifferentialInvolution_reverse
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidueEquiv_uniformizerLogDifferentialClass
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidueEquiv_unique
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSimplePoleTraceResidue_functionFieldDifferentialTrace_simplePoleResidue_eq_sum_directFactorTraces
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseDifferentialTraceTransport_transported_functionFieldDifferentialTrace_eq_rationalDifferentialInvolution
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_directFactorGlobalPlace_infinityFibreEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_smul
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
private theorem idealXResidueEquiv_quotientResidueEquiv_C (a : k) :
    idealXResidueEquiv (k := k)
        (Ideal.Factors.quotientResidueEquiv
          (Polynomial.idealX k).asIdeal
          (Ideal.Quotient.mk (Polynomial.idealX k).asIdeal
            (Polynomial.C a))) = a := by
  rw [idealXResidueEquiv, RingEquiv.trans_apply,
    RingEquiv.symm_apply_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  change Polynomial.quotientSpanXSubCAlgEquiv (0 : k)
      (Ideal.Quotient.mk (Ideal.span
        ({Polynomial.X - Polynomial.C (0 : k)} : Set k[X]))
        (Polynomial.C a)) = a
  rw [Polynomial.quotientSpanXSubCAlgEquiv_mk]
  simp
private theorem idealXResidueEquiv_symm_apply (a : k) :
    (idealXResidueEquiv (k := k)).symm a =
      Ideal.Factors.quotientResidueEquiv
        (Polynomial.idealX k).asIdeal
        (Ideal.Quotient.mk (Polynomial.idealX k).asIdeal
          (Polynomial.C a)) := by
  apply (idealXResidueEquiv (k := k)).injective
  rw [(idealXResidueEquiv (k := k)).apply_symm_apply,
    idealXResidueEquiv_quotientResidueEquiv_C]
private theorem directBaseResidueRationalAdicEquiv_idealXResidueEquiv_symm
    (a : k) :
    DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k
        (Polynomial.idealX k) ((idealXResidueEquiv (k := k)).symm a) =
      GlobalPlace.constantsToResidue
        (InverseRationalInfinityTransport.xAdicPlace k) a := by
  rw [idealXResidueEquiv_symm_apply,
    DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv,
    RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
    GlobalPlace.rationalAdicIdealResidueEquiv_mk]
  change (InverseRationalInfinityTransport.xAdicPlace k).residue
      (GlobalPlace.rationalAdicPolynomialToValuationRing
        (Polynomial.idealX k) (Polynomial.C a)) =
    (InverseRationalInfinityTransport.xAdicPlace k).residue
      (GlobalPlace.constantsToValuationRing
        (InverseRationalInfinityTransport.xAdicPlace k) a)
  apply congrArg
    (GlobalPlace.residue (InverseRationalInfinityTransport.xAdicPlace k))
  apply Subtype.ext
  simp only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    GlobalPlace.coe_constantsToValuationRing, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]
private theorem directBaseResidueRationalAdicEquiv_idealXResidueEquiv
    (z : (Polynomial.idealX k).asIdeal.ResidueField) :
    letI : Algebra k
        (InverseRationalInfinityTransport.xAdicPlace k).residueField :=
      GlobalPlace.residueAlgebra
        (InverseRationalInfinityTransport.xAdicPlace k)
    letI : Algebra (Polynomial.idealX k).asIdeal.ResidueField
        (InverseRationalInfinityTransport.xAdicPlace k).residueField :=
      (DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k
        (Polynomial.idealX k)).toRingHom.toAlgebra
    algebraMap k
        (InverseRationalInfinityTransport.xAdicPlace k).residueField
        (idealXResidueEquiv (k := k) z) =
      algebraMap (Polynomial.idealX k).asIdeal.ResidueField
        (InverseRationalInfinityTransport.xAdicPlace k).residueField z := by
  letI : Algebra k
      (InverseRationalInfinityTransport.xAdicPlace k).residueField :=
    GlobalPlace.residueAlgebra
      (InverseRationalInfinityTransport.xAdicPlace k)
  letI : Algebra (Polynomial.idealX k).asIdeal.ResidueField
      (InverseRationalInfinityTransport.xAdicPlace k).residueField :=
    (DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k
      (Polynomial.idealX k)).toRingHom.toAlgebra
  change GlobalPlace.constantsToResidue
      (InverseRationalInfinityTransport.xAdicPlace k)
        (idealXResidueEquiv (k := k) z) =
    DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k
      (Polynomial.idealX k) z
  have heq := (directBaseResidueRationalAdicEquiv_idealXResidueEquiv_symm
    (k := k) (idealXResidueEquiv (k := k) z)).symm
  rw [(idealXResidueEquiv (k := k)).symm_apply_apply] at heq
  exact heq
private theorem trace_directBaseResidueRationalAdicEquiv_idealX
    (z : (Polynomial.idealX k).asIdeal.ResidueField) :
    letI : Algebra k
        (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField :=
      GlobalPlace.residueAlgebra
        (GlobalPlace.rationalAdic (Polynomial.idealX k))
    Algebra.trace k
        (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField
        (DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k
          (Polynomial.idealX k) z) =
      idealXResidueEquiv (k := k) z := by
  let K := (Polynomial.idealX k).asIdeal.ResidueField
  let e := idealXResidueEquiv (k := k)
  let E := DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv k
    (Polynomial.idealX k)
  letI : Algebra k
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField :=
    GlobalPlace.residueAlgebra
      (GlobalPlace.rationalAdic (Polynomial.idealX k))
  change Algebra.trace k
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField
      (E z) = e z
  letI : Algebra K
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField :=
    E.toRingHom.toAlgebra
  letI : Algebra k K := e.symm.toRingHom.toAlgebra
  letI : Finite K := Finite.of_equiv k e.symm.toEquiv
  letI : Finite
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField :=
    Finite.of_equiv K E.toEquiv
  letI : FiniteDimensional k
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField :=
    GlobalPlace.residueField_finiteDimensional
      (GlobalPlace.rationalAdic (Polynomial.idealX k))
  letI : Module.Finite K
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField :=
    (Module.finite_iff_finite).mpr inferInstance
  have hdegreeCompat :
      RingHom.comp (algebraMap K
          (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField)
          (RingEquiv.refl K).toRingHom =
        RingHom.comp E.toRingHom (algebraMap K K) := by
    apply DFunLike.ext _ _
    intro r
    rfl
  have hdegreeOne := Algebra.trace_eq_of_equiv_equiv
    (RingEquiv.refl K) E hdegreeCompat z
  have htraceBase : Algebra.trace K
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField
      (E z) = z := by
    exact hdegreeOne.symm.trans (Algebra.trace_self_apply z)
  have hcompat : RingHom.comp
        (algebraMap k
          (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField)
        e.toRingHom =
      RingHom.comp
        (RingEquiv.refl
          (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField).toRingHom
        (algebraMap K
          (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField) := by
    apply DFunLike.ext _ _
    intro r
    exact directBaseResidueRationalAdicEquiv_idealXResidueEquiv
      (k := k) r
  have htraceChange := Algebra.trace_eq_of_equiv_equiv
    e (RingEquiv.refl
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField)
      hcompat (E z)
  have htraceChange' := congrArg e htraceChange
  simp only [e, RingEquiv.apply_symm_apply, RingEquiv.refl_apply] at htraceChange'
  rw [htraceBase] at htraceChange'
  exact htraceChange'.symm
section DirectFactor
variable {F : Type*} [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] infinityDirectConstantAlgebra
attribute [local instance] infinityDirectConstantScalarTower
private theorem directFactorBaseResidueMap_idealXResidueEquiv_symm
    (P : (factors (Ideal.map (algebraMap k[X] (B k F))
      (Polynomial.idealX k).asIdeal)).toFinset) (a : k) :
    DirectFactorTraceResidue.directFactorBaseResidueMap k F
        (Polynomial.idealX k) P ((idealXResidueEquiv (k := k)).symm a) =
      GlobalPlace.constantsToResidue
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F
            (Polynomial.idealX k) P)) a := by
  let upperIdeal : Ideal (B k F) := (P : Ideal (B k F))
  let upper := AffinePlace.globalPlace k F
    (DirectIntegralDifferentialResidue.directFactorPlace k F
      (Polynomial.idealX k) P)
  letI : upperIdeal.IsMaximal :=
    (Ideal.Factors.isPrime (Polynomial.idealX k).asIdeal P).isMaximal
      (Ideal.Factors.ne_bot (Polynomial.idealX k).asIdeal P)
  letI : Algebra (Localization.AtPrime (Polynomial.idealX k).asIdeal)
      (Localization.AtPrime upperIdeal) :=
    Localization.AtPrime.algebraOfLiesOver
      (Polynomial.idealX k).asIdeal upperIdeal
  letI : Algebra (Localization.AtPrime upperIdeal)
      upperIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra
      (R₀ := Localization.AtPrime upperIdeal) (Localization.AtPrime upperIdeal)
  have hbase :
      algebraMap (Polynomial.idealX k).asIdeal.ResidueField
          upperIdeal.ResidueField
          ((idealXResidueEquiv (k := k)).symm a) =
        algebraMap (B k F) upperIdeal.ResidueField
          (algebraMap k[X] (B k F) (Polynomial.C a)) := by
    rw [idealXResidueEquiv_symm_apply,
      Ideal.Factors.quotientResidueEquiv_mk]
    change algebraMap (Polynomial.idealX k).asIdeal.ResidueField
        upperIdeal.ResidueField
        (IsLocalRing.residue
          (Localization.AtPrime (Polynomial.idealX k).asIdeal)
          (algebraMap k[X]
            (Localization.AtPrime (Polynomial.idealX k).asIdeal)
            (Polynomial.C a))) =
      IsLocalRing.residue (Localization.AtPrime upperIdeal)
        (algebraMap (B k F) (Localization.AtPrime upperIdeal)
          (algebraMap k[X] (B k F) (Polynomial.C a)))
    rw [IsLocalRing.ResidueField.algebraMap_residue
      (R := Localization.AtPrime (Polynomial.idealX k).asIdeal)
      (S := Localization.AtPrime upperIdeal)]
    apply congrArg (IsLocalRing.residue (Localization.AtPrime upperIdeal))
    rw [← IsScalarTower.algebraMap_apply k[X]
      (Localization.AtPrime (Polynomial.idealX k).asIdeal)
      (Localization.AtPrime upperIdeal)]
    rw [← IsScalarTower.algebraMap_apply k[X] (B k F)
      (Localization.AtPrime upperIdeal)]
  change DirectFactorResidueTransport.directFactorResidueEquiv k F
      (Polynomial.idealX k) P
      (algebraMap (Polynomial.idealX k).asIdeal.ResidueField
        upperIdeal.ResidueField ((idealXResidueEquiv (k := k)).symm a)) =
    upper.residue (GlobalPlace.constantsToValuationRing upper a)
  rw [hbase,
    DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap]
  apply congrArg upper.residue
  apply Subtype.ext
  change algebraMap (B k F) F
      (algebraMap k[X] (B k F) (Polynomial.C a)) = algebraMap k F a
  rfl
private theorem directFactorBaseResidueMap_idealXResidueEquiv
    (P : (factors (Ideal.map (algebraMap k[X] (B k F))
      (Polynomial.idealX k).asIdeal)).toFinset)
    (z : (Polynomial.idealX k).asIdeal.ResidueField) :
    DirectFactorTraceResidue.directFactorBaseResidueMap k F
        (Polynomial.idealX k) P z =
      GlobalPlace.constantsToResidue
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F
            (Polynomial.idealX k) P))
        (idealXResidueEquiv (k := k) z) := by
  simpa only [RingEquiv.symm_apply_apply] using
    directFactorBaseResidueMap_idealXResidueEquiv_symm
      (k := k) (F := F) P (idealXResidueEquiv (k := k) z)
private theorem idealXResidueEquiv_directFactorPlaceTrace
    (P : (factors (Ideal.map (algebraMap k[X] (B k F))
      (Polynomial.idealX k).asIdeal)).toFinset)
    (x : (AffinePlace.globalPlace k F
      (DirectIntegralDifferentialResidue.directFactorPlace k F
        (Polynomial.idealX k) P)).residueField) :
    idealXResidueEquiv (k := k)
        (DirectFactorTraceResidue.directFactorPlaceTrace k F
          (Polynomial.idealX k) P x) =
      letI : Algebra k
          (AffinePlace.globalPlace k F
            (DirectIntegralDifferentialResidue.directFactorPlace k F
              (Polynomial.idealX k) P)).residueField :=
        GlobalPlace.residueAlgebra
          (AffinePlace.globalPlace k F
            (DirectIntegralDifferentialResidue.directFactorPlace k F
              (Polynomial.idealX k) P))
      Algebra.trace k
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F
            (Polynomial.idealX k) P)).residueField x := by
  let K := (Polynomial.idealX k).asIdeal.ResidueField
  let upper := AffinePlace.globalPlace k F
    (DirectIntegralDifferentialResidue.directFactorPlace k F
      (Polynomial.idealX k) P)
  let e := idealXResidueEquiv (k := k)
  letI : Algebra K upper.residueField :=
    (DirectFactorTraceResidue.directFactorBaseResidueMap k F
      (Polynomial.idealX k) P).toAlgebra
  letI : Algebra k upper.residueField :=
    GlobalPlace.residueAlgebra upper
  change e (Algebra.trace K upper.residueField x) =
    Algebra.trace k upper.residueField x
  have he : RingHom.comp (algebraMap k upper.residueField) e.toRingHom =
      RingHom.comp (RingEquiv.refl upper.residueField).toRingHom
        (algebraMap K upper.residueField) := by
    apply DFunLike.ext _ _
    intro z
    change GlobalPlace.constantsToResidue upper (e z) =
      DirectFactorTraceResidue.directFactorBaseResidueMap k F
        (Polynomial.idealX k) P z
    exact (directFactorBaseResidueMap_idealXResidueEquiv
      (k := k) (F := F) P z).symm
  have htrace := Algebra.trace_eq_of_equiv_equiv
    e (RingEquiv.refl upper.residueField) he x
  have htrace' := congrArg e htrace
  simpa only [RingEquiv.apply_symm_apply, RingEquiv.refl_apply] using htrace'
private theorem
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_idealXFactors
    (omega : Differential k F)
    (homega : ∀ P : (factors
      (Ideal.map (algebraMap k[X] (B k F))
        (Polynomial.idealX k).asIdeal)).toFinset,
      omega ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F
            (Polynomial.idealX k) P))) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (InverseRationalInfinityTransport.xAdicPlace k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (InverseRationalInfinityTransport.xAdicPlace k)
          (functionFieldDifferentialTrace (k := k) (F := F) omega) htrace =
        ∑ P : (factors
            (Ideal.map (algebraMap k[X] (B k F))
              (Polynomial.idealX k).asIdeal)).toFinset,
          Differential.simplePoleTraceResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F
              (DirectIntegralDifferentialResidue.directFactorPlace k F
                (Polynomial.idealX k) P)) omega (homega P) := by
  classical
  obtain ⟨htrace, hresidue⟩ :=
    DirectSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleResidue_eq_sum_directFactorTraces
      (k := k) (F := F) (Polynomial.idealX k) omega homega
  refine ⟨htrace, ?_⟩
  letI : Algebra k
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField :=
    GlobalPlace.residueAlgebra
      (GlobalPlace.rationalAdic (Polynomial.idealX k))
  change Algebra.trace k
      (GlobalPlace.rationalAdic (Polynomial.idealX k)).residueField
      (Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic (Polynomial.idealX k))
        ⟨functionFieldDifferentialTrace (k := k) (F := F) omega,
          htrace⟩) = _
  rw [hresidue,
    trace_directBaseResidueRationalAdicEquiv_idealX (k := k), map_sum]
  apply Finset.sum_congr rfl
  intro P _
  let upper := AffinePlace.globalPlace k F
    (DirectIntegralDifferentialResidue.directFactorPlace k F
      (Polynomial.idealX k) P)
  letI : Algebra k upper.residueField :=
    GlobalPlace.residueAlgebra upper
  change idealXResidueEquiv (k := k)
      (DirectFactorTraceResidue.directFactorPlaceTrace k F
        (Polynomial.idealX k) P
        (Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F
            (DirectIntegralDifferentialResidue.directFactorPlace k F
              (Polynomial.idealX k) P)) ⟨omega, homega P⟩)) =
    Algebra.trace k
      (AffinePlace.globalPlace k F
        (DirectIntegralDifferentialResidue.directFactorPlace k F
          (Polynomial.idealX k) P)).residueField
      (Differential.simplePoleResidue (k := k) (F := F)
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F
            (Polynomial.idealX k) P)) ⟨omega, homega P⟩)
  exact idealXResidueEquiv_directFactorPlaceTrace
    (k := k) (F := F) P _
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
private theorem castGlobalPlace_eq_mk {A A' : Algebra k F} (hA : A = A')
    (P : GlobalPlaceAt A) :
    castGlobalPlace hA P =
      @GlobalPlace.mk k F _ _ _ A'
        (@GlobalPlace.valuation k F _ _ _ A P)
        (@GlobalPlace.normalized k F _ _ _ A P) := by
  cases hA
  cases P
  rfl
private theorem castDifferential_mem_simplePole_of_mem
    {A A' : Algebra k F} (hA : A = A')
    (P : GlobalPlaceAt A) (Q : GlobalPlaceAt A')
    (hP : castGlobalPlace hA P = Q) (omega : DifferentialAt A')
    (homega : omega ∈
      @Differential.simplePoleDifferentialLattice k F _ _ _ A' Q) :
    castDifferential hA.symm omega ∈
      @Differential.simplePoleDifferentialLattice k F _ _ _ A P := by
  cases hA
  change P = Q at hP
  subst Q
  exact homega
private theorem castDifferential_apply_symm_apply
    {A A' : Algebra k F} (hA : A = A') (omega : DifferentialAt A') :
    castDifferential hA (castDifferential hA.symm omega) = omega := by
  cases hA
  rfl
private theorem functionFieldDifferentialTraceAt_eq_of_algebra_eq
    {A A' : Algebra k F} (hA : A = A')
    (ρ : Algebra (RatFunc k) F)
    (τ : letI : Algebra k F := A
      letI : Algebra (RatFunc k) F := ρ
      IsScalarTower k (RatFunc k) F)
    (τ' : letI : Algebra k F := A'
      letI : Algebra (RatFunc k) F := ρ
      IsScalarTower k (RatFunc k) F)
    (σ : letI : Algebra (RatFunc k) F := ρ
      Algebra.IsSeparable (RatFunc k) F)
    (φ : letI : Algebra (RatFunc k) F := ρ
      FiniteDimensional (RatFunc k) F)
    (omega : DifferentialAt A) (omega' : DifferentialAt A')
    (homega : castDifferential hA omega = omega') :
    functionFieldDifferentialTraceAt A ρ τ σ φ omega =
      functionFieldDifferentialTraceAt A' ρ τ' σ φ omega' := by
  cases hA
  change omega = omega' at homega
  subst omega'
  rfl
private theorem simplePoleTraceResidueAt_eq_of_algebra_eq
    {A A' : Algebra k F} (hA : A = A')
    (ρ : Algebra (RatFunc k) F)
    (τ : letI : Algebra k F := A
      letI : Algebra (RatFunc k) F := ρ
      IsScalarTower k (RatFunc k) F)
    (τ' : letI : Algebra k F := A'
      letI : Algebra (RatFunc k) F := ρ
      IsScalarTower k (RatFunc k) F)
    (σ : letI : Algebra (RatFunc k) F := ρ
      Algebra.IsSeparable (RatFunc k) F)
    (φ : letI : Algebra (RatFunc k) F := ρ
      FiniteDimensional (RatFunc k) F)
    (P : GlobalPlaceAt A) (Q : GlobalPlaceAt A')
    (hP : castGlobalPlace hA P = Q)
    (omega : DifferentialAt A) (omega' : DifferentialAt A')
    (homega : castDifferential hA omega = omega')
    (homegaP : omega ∈
      @Differential.simplePoleDifferentialLattice k F _ _ _ A P)
    (homegaQ : omega' ∈
      @Differential.simplePoleDifferentialLattice k F _ _ _ A' Q) :
    simplePoleTraceResidueAt A ρ τ σ φ P omega homegaP =
      simplePoleTraceResidueAt A' ρ τ' σ φ Q omega' homegaQ := by
  cases hA
  change P = Q at hP
  subst Q
  change omega = omega' at homega
  subst omega'
  rfl
private theorem simplePoleTraceResidue_eq_of_place_eq
    {P Q : GlobalPlace k F} (hPQ : P = Q) (omega : Differential k F)
    (hP : omega ∈ Differential.simplePoleDifferentialLattice P)
    (hQ : omega ∈ Differential.simplePoleDifferentialLattice Q) :
    Differential.simplePoleTraceResidue (k := k) (F := F) P omega hP =
      Differential.simplePoleTraceResidue (k := k) (F := F) Q omega hQ := by
  subst Q
  rfl
omit [Finite k] in
private theorem inverseAffineConstantAlgebra_eq_direct :
    letI : Algebra (RatFunc k) F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] (RatFunc k) F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable (RatFunc k) F := inverseIsSeparable
    AffinePlace.constantAlgebra k F =
      @AffinePlace.constantAlgebra k F _ _ oldPolynomialAlgebra := by
  letI : Algebra (RatFunc k) F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] (RatFunc k) F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable (RatFunc k) F := inverseIsSeparable
  apply Algebra.algebra_ext
  intro c
  change algebraMap k[X] F (Polynomial.C c) =
    @algebraMap k[X] F _ _ oldPolynomialAlgebra (Polynomial.C c)
  change (@algebraMap (RatFunc k) F _ _ oldRationalAlgebra)
      (InverseAffinePlace.rationalInvolution k
        (algebraMap k[X] (RatFunc k) (Polynomial.C c))) =
    @algebraMap k[X] F _ _ oldPolynomialAlgebra (Polynomial.C c)
  change (@algebraMap (RatFunc k) F _ _ oldRationalAlgebra)
      (InverseAffinePlace.rationalInvolution k
        (algebraMap k (RatFunc k) c)) =
    @algebraMap k[X] F _ _ oldPolynomialAlgebra (Polynomial.C c)
  rw [(InverseAffinePlace.rationalInvolution k).commutes]
  simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
    (@IsScalarTower.algebraMap_apply k[X] (RatFunc k) F _ _ _ _
      oldRationalAlgebra oldPolynomialAlgebra oldScalarTower
      (Polynomial.C c)).symm
private theorem
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre_raw :
    letI : Algebra (RatFunc k) F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] (RatFunc k) F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable (RatFunc k) F := inverseIsSeparable
    ∀ (omega : Differential k F)
      (homega : ∀ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
        omega ∈ Differential.simplePoleDifferentialLattice
          (InverseAffinePlace.globalPlace
            (oldRationalAlgebra := oldRationalAlgebra) k F D)),
      ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
          Differential.simplePoleDifferentialLattice
            (InverseRationalInfinityTransport.xAdicPlace k),
        Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
            (InverseRationalInfinityTransport.xAdicPlace k)
            (functionFieldDifferentialTrace (k := k) (F := F) omega) htrace =
          ∑ D : InverseAffinePlace.infinityFibre
              (oldRationalAlgebra := oldRationalAlgebra) k F,
            Differential.simplePoleTraceResidue (k := k) (F := F)
              (InverseAffinePlace.globalPlace
                (oldRationalAlgebra := oldRationalAlgebra) k F D)
              omega (homega D) := by
  letI : Algebra (RatFunc k) F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] (RatFunc k) F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable (RatFunc k) F := inverseIsSeparable
  classical
  intro omega homega
  let e := InverseFibreDirectFactor.infinityFibreEquivDirectFactors
    (oldRationalAlgebra := oldRationalAlgebra) k F
  have hfactor : ∀ P : (factors
      (Ideal.map (algebraMap k[X] (B k F))
        (Polynomial.idealX k).asIdeal)).toFinset,
      omega ∈ Differential.simplePoleDifferentialLattice
        (AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F
            (Polynomial.idealX k) P)) := by
    intro P
    let D := e.symm P
    have hD := homega D
    rw [← InverseFibreDirectFactor.directFactorGlobalPlace_infinityFibreEquiv
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F D] at hD
    have he : e D = P := e.apply_symm_apply P
    rw [he] at hD
    exact hD
  obtain ⟨htrace, hresidue⟩ :=
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_idealXFactors
      (k := k) (F := F) omega hfactor
  refine ⟨htrace, hresidue.trans ?_⟩
  apply Fintype.sum_equiv e.symm
  intro P
  let D := e.symm P
  have hplace :=
    InverseFibreDirectFactor.directFactorGlobalPlace_infinityFibreEquiv
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F D
  have he : e D = P := e.apply_symm_apply P
  have hplace' :
      AffinePlace.globalPlace k F
          (DirectIntegralDifferentialResidue.directFactorPlace k F
            (Polynomial.idealX k) P) =
        InverseAffinePlace.globalPlace
          (oldRationalAlgebra := oldRationalAlgebra) k F D := by
    rw [← he]
    exact hplace
  exact simplePoleTraceResidue_eq_of_place_eq
    (k := k) (F := F) hplace' omega _ _
private theorem
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre_repackaged
    (omega : Differential k F)
    (homega : ∀ D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F,
      omega ∈ Differential.simplePoleDifferentialLattice
        (InverseAffinePlace.infinityFibreGlobalPlace
          (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
          (τ := oldScalarTower) (φ := oldFunctionField)
          (σ := oldSeparable) (k := k) (F := F) D)) :
    letI : Algebra (RatFunc k) F := inverseRationalAlgebra
    letI : IsScalarTower k (RatFunc k) F := inverseConstantScalarTower
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) (k := k) (F := F)
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable (RatFunc k) F := inverseIsSeparable
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (InverseRationalInfinityTransport.xAdicPlace k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (InverseRationalInfinityTransport.xAdicPlace k)
          (functionFieldDifferentialTrace (k := k) (F := F) omega) htrace =
        ∑ D : InverseAffinePlace.infinityFibre
            (oldRationalAlgebra := oldRationalAlgebra) k F,
          Differential.simplePoleTraceResidue (k := k) (F := F)
            (InverseAffinePlace.infinityFibreGlobalPlace
              (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
              (τ := oldScalarTower) (φ := oldFunctionField)
              (σ := oldSeparable) (k := k) (F := F) D)
            omega (homega D) := by
  classical
  let oldConstant : Algebra k F :=
    @AffinePlace.constantAlgebra k F _ _ oldPolynomialAlgebra
  letI : Algebra (RatFunc k) F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] (RatFunc k) F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable (RatFunc k) F := inverseIsSeparable
  let rawConstant : Algebra k F :=
    @AffinePlace.constantAlgebra k F _ _ inversePolynomialAlgebra
  let rawTower :
      letI : Algebra k F := rawConstant
      IsScalarTower k (RatFunc k) F := by
    exact affineConstantScalarTower (k := k) (F := F)
  have hconstant : rawConstant = oldConstant := by
    simpa only [rawConstant, oldConstant, infinityDirectConstantAlgebra] using
      (inverseAffineConstantAlgebra_eq_direct
        (k := k) (F := F)
        (oldPolynomialAlgebra := oldPolynomialAlgebra)
        (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower)
        (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable))
  letI : Algebra k F := oldConstant
  letI : IsScalarTower k (RatFunc k) F := inverseConstantScalarTower
    (oldPolynomialAlgebra := oldPolynomialAlgebra)
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) (k := k) (F := F)
  let targetTower :
      letI : Algebra k F := oldConstant
      IsScalarTower k (RatFunc k) F := inferInstance
  let inverseFiniteDimensional : FiniteDimensional (RatFunc k) F :=
    inferInstance
  let omegaRaw : DifferentialAt rawConstant :=
    castDifferential hconstant.symm omega
  let rawPlace (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
      GlobalPlaceAt rawConstant :=
    InverseAffinePlace.globalPlace
      (oldRationalAlgebra := oldRationalAlgebra) k F D
  let packagedPlace (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
      GlobalPlaceAt oldConstant :=
    InverseAffinePlace.infinityFibreGlobalPlace
      (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
      (τ := oldScalarTower) (φ := oldFunctionField)
      (σ := oldSeparable) (κ := oldConstant) D
  have hplace (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
      castGlobalPlace hconstant (rawPlace D) = packagedPlace D := by
    change castGlobalPlace hconstant (rawPlace D) =
      @GlobalPlace.mk k F _ _ _ oldConstant
        (@GlobalPlace.valuation k F _ _ _ rawConstant (rawPlace D))
        (@GlobalPlace.normalized k F _ _ _ rawConstant (rawPlace D))
    exact castGlobalPlace_eq_mk hconstant (rawPlace D)
  have homegaRaw (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
      omegaRaw ∈ @Differential.simplePoleDifferentialLattice
        k F _ _ _ rawConstant (rawPlace D) := by
    apply castDifferential_mem_simplePole_of_mem
      hconstant (rawPlace D) (packagedPlace D) (hplace D) omega
    simpa only [packagedPlace, oldConstant, infinityDirectConstantAlgebra] using
      homega D
  obtain ⟨htraceRaw, hresidueRaw⟩ :=
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre_raw
      (k := k) (F := F)
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower)
      (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) omegaRaw homegaRaw
  have homegaCast : castDifferential hconstant omegaRaw = omega := by
    exact castDifferential_apply_symm_apply hconstant omega
  have htraceEq :
      functionFieldDifferentialTraceAt rawConstant inverseRationalAlgebra
          rawTower inverseIsSeparable inverseFiniteDimensional omegaRaw =
        functionFieldDifferentialTraceAt oldConstant inverseRationalAlgebra
          targetTower inverseIsSeparable inverseFiniteDimensional omega := by
    exact functionFieldDifferentialTraceAt_eq_of_algebra_eq
      hconstant inverseRationalAlgebra rawTower targetTower
      inverseIsSeparable inverseFiniteDimensional omegaRaw omega homegaCast
  change functionFieldDifferentialTraceAt rawConstant inverseRationalAlgebra
      rawTower inverseIsSeparable inverseFiniteDimensional omegaRaw ∈
    Differential.simplePoleDifferentialLattice
      (InverseRationalInfinityTransport.xAdicPlace k) at htraceRaw
  have htrace :
      functionFieldDifferentialTraceAt oldConstant inverseRationalAlgebra
          targetTower inverseIsSeparable inverseFiniteDimensional omega ∈
        Differential.simplePoleDifferentialLattice
          (InverseRationalInfinityTransport.xAdicPlace k) := by
    simpa only [htraceEq] using htraceRaw
  refine ⟨htrace, ?_⟩
  change Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
      (InverseRationalInfinityTransport.xAdicPlace k)
      (functionFieldDifferentialTraceAt oldConstant inverseRationalAlgebra
        targetTower inverseIsSeparable inverseFiniteDimensional omega) htrace = _
  calc
    _ = Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
        (InverseRationalInfinityTransport.xAdicPlace k)
        (functionFieldDifferentialTraceAt rawConstant inverseRationalAlgebra
          rawTower inverseIsSeparable inverseFiniteDimensional omegaRaw)
        htraceRaw := by
      simpa only [htraceEq]
    _ = ∑ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
        simplePoleTraceResidueAt rawConstant inverseRationalAlgebra
          rawTower inverseIsSeparable inverseFiniteDimensional
          (rawPlace D) omegaRaw (homegaRaw D) := by
      exact hresidueRaw
    _ = ∑ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
        simplePoleTraceResidueAt oldConstant inverseRationalAlgebra
          targetTower inverseIsSeparable inverseFiniteDimensional
          (packagedPlace D) omega (by
            simpa only [packagedPlace, oldConstant,
              infinityDirectConstantAlgebra] using homega D) := by
      apply Finset.sum_congr rfl
      intro D _
      exact simplePoleTraceResidueAt_eq_of_algebra_eq
        hconstant inverseRationalAlgebra rawTower targetTower
        inverseIsSeparable inverseFiniteDimensional
        (rawPlace D) (packagedPlace D) (hplace D) omegaRaw omega
        homegaCast (homegaRaw D) _
    _ = _ := by
      rfl
end InfinityFibre
end QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
open scoped Polynomial RatFunc BigOperators
open FunctionFieldDifferential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k] [Finite k]
variable {F : Type*} [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra (RatFunc k) F]
variable [oldScalarTower : IsScalarTower k[X] (RatFunc k) F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.directConstantAlgebra
attribute [local instance] directConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.directConstantScalarTower
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
namespace QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
theorem _root_.solution
    (omega : Differential k F)
    (homega : ∀ D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F,
      omega ∈ Differential.simplePoleDifferentialLattice
        (InverseAffinePlace.infinityFibreGlobalPlace
          (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
          (τ := oldScalarTower) (φ := oldFunctionField)
          (σ := oldSeparable) (k := k) (F := F) D)) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalInfinity k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k)
          (functionFieldDifferentialTrace (k := k) (F := F) omega) htrace =
        ∑ D : InverseAffinePlace.infinityFibre
            (oldRationalAlgebra := oldRationalAlgebra) k F,
          Differential.simplePoleTraceResidue (k := k) (F := F)
            (InverseAffinePlace.infinityFibreGlobalPlace
              (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
              (τ := oldScalarTower) (φ := oldFunctionField)
              (σ := oldSeparable) (k := k) (F := F) D)
            omega (homega D) := by
  classical
  let P (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) : GlobalPlace k F :=
    InverseAffinePlace.infinityFibreGlobalPlace
      (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
      (τ := oldScalarTower) (φ := oldFunctionField)
      (σ := oldSeparable) (k := k) (F := F) D
  let oldTrace : Differential k (RatFunc k) :=
    functionFieldDifferentialTrace (k := k) (F := F) omega
  let oldResidueEquiv (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :=
    Differential.simplePoleResidueEquiv (k := k) (F := F) (P D)
  let oldTraceResidue (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) : k :=
    Differential.simplePoleTraceResidue (k := k) (F := F)
      (P D) omega (homega D)
  have oldResidueEquiv_normalized
      (D : InverseAffinePlace.infinityFibre
        (oldRationalAlgebra := oldRationalAlgebra) k F) :
      oldResidueEquiv D
          (Differential.uniformizerLogDifferentialClass
            (k := k) (F := F) (P D)) = 1 := by
    exact
      Differential.simplePoleResidueEquiv_uniformizerLogDifferentialClass
        (k := k) (F := F) (P D)
  letI : Algebra (RatFunc k) F := inverseRationalAlgebra
  letI : IsScalarTower k (RatFunc k) F := inverseConstantScalarTower
    (oldPolynomialAlgebra := oldPolynomialAlgebra)
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) (k := k) (F := F)
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable (RatFunc k) F := inverseIsSeparable
  have hresidueEquiv
      (D : InverseAffinePlace.infinityFibre
        (oldRationalAlgebra := oldRationalAlgebra) k F) :
      oldResidueEquiv D =
        Differential.simplePoleResidueEquiv (k := k) (F := F) (P D) := by
    exact Differential.simplePoleResidueEquiv_unique
      (k := k) (F := F) (P D) (oldResidueEquiv D)
        (oldResidueEquiv_normalized D)
  have htraceResidue
      (D : InverseAffinePlace.infinityFibre
        (oldRationalAlgebra := oldRationalAlgebra) k F) :
      Differential.simplePoleTraceResidue (k := k) (F := F)
          (P D) omega (homega D) = oldTraceResidue D := by
    letI : Algebra k (P D).residueField :=
      GlobalPlace.residueAlgebra (P D)
    letI : FiniteDimensional k (P D).residueField :=
      GlobalPlace.residueField_finiteDimensional
        (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
        (τ := oldScalarTower) (φ := oldFunctionField)
        (σ := oldSeparable) (P D)
    change Algebra.trace k (P D).residueField
        (Differential.simplePoleResidueEquiv (k := k) (F := F) (P D)
          (Submodule.Quotient.mk
            (⟨omega, homega D⟩ :
              Differential.simplePoleDifferentialLattice (P D)))) =
      oldTraceResidue D
    rw [← hresidueEquiv D]
    rfl
  obtain ⟨htraceInverse, hsumInverse⟩ :=
    functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre_repackaged
      (k := k) (F := F)
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower)
      (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) omega homega
  have htransport :
      functionFieldDifferentialTrace (k := k) (F := F) omega =
        InverseRationalInfinityTransport.rationalDifferentialInvolution
          (k := k) oldTrace := by
    exact
      InverseDifferentialTraceTransport.transported_functionFieldDifferentialTrace_eq_rationalDifferentialInvolution
        (oldPolynomialAlgebra := oldPolynomialAlgebra)
        (oldRationalAlgebra := oldRationalAlgebra)
        (oldScalarTower := oldScalarTower)
        (oldFunctionField := oldFunctionField)
        (oldSeparable := oldSeparable) k F omega
  obtain ⟨htraceBack, hresidueBack⟩ :=
    simplePoleTraceResidue_rationalDifferentialInvolution_reverse
      (k := k)
      (functionFieldDifferentialTrace (k := k) (F := F) omega)
      htraceInverse
  have hbackEq :
      InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
          (functionFieldDifferentialTrace (k := k) (F := F) omega) =
        oldTrace := by
    rw [htransport, rationalDifferentialInvolution_involutive]
  have htrace : oldTrace ∈ Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalInfinity k) := by
    rw [← hbackEq]
    exact htraceBack
  refine ⟨htrace, ?_⟩
  change Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
      (GlobalPlace.rationalInfinity k) oldTrace htrace = _
  calc
    _ = Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (InverseRationalInfinityTransport.rationalDifferentialInvolution
          (k := k)
          (functionFieldDifferentialTrace (k := k) (F := F) omega))
        htraceBack := by
      simpa only [hbackEq]
    _ = Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
        (InverseRationalInfinityTransport.xAdicPlace k)
        (functionFieldDifferentialTrace (k := k) (F := F) omega)
        htraceInverse := hresidueBack
    _ = ∑ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
        Differential.simplePoleTraceResidue (k := k) (F := F)
          (P D) omega (homega D) := by
      simpa only [P] using hsumInverse
    _ = ∑ D : InverseAffinePlace.infinityFibre
          (oldRationalAlgebra := oldRationalAlgebra) k F,
        oldTraceResidue D := by
      apply Finset.sum_congr rfl
      intro D _
      exact htraceResidue D
    _ = _ := by
      rfl
end QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
