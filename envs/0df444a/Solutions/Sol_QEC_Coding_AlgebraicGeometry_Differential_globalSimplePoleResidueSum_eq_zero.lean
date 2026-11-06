-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:17:19.761341+00:00
-- url     : https://prove2.me/submissions/c2c0237b-6c41-45bc-add2-ee7d245fbc59

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_GlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_ratFunc
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferential_eq_coordinate_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finsupp_sum_eq_affine_add_infinityFibre
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
open scoped BigOperators Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldGlobalResidue
open UniqueFactorizationMonoid
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] functionFieldGlobalResidue_Algebra_1
attribute [local instance] functionFieldGlobalResidue_ScalarTower_1
private theorem globalSimplePoleResidueSum_eq_traceResidueSum
    (omega : Differential k F)
    (homega : Differential.IsGlobalSimplePole (k := k) (F := F) omega) :
    Differential.globalSimplePoleResidueSum (k := k) (F := F) omega homega =
      Differential.globalSimplePoleResidueSum (k := k) (F := RatFunc k)
        (functionFieldDifferentialTrace (k := k) (F := F) omega)
        (functionFieldDifferentialTrace_isGlobalSimplePole
          (k := k) (F := F) omega homega) := by
  classical
  let traceOmega := functionFieldDifferentialTrace (k := k) (F := F) omega
  let htraceGlobal : Differential.IsGlobalSimplePole
      (k := k) (F := RatFunc k) traceOmega :=
    functionFieldDifferentialTrace_isGlobalSimplePole
      (k := k) (F := F) omega homega
  let sourceResidues := Differential.globalSimplePoleResidue
    (k := k) (F := F) omega homega
  let affineResidues := GlobalPlace.affineFinsupp (k := k) (F := F)
    sourceResidues
  let infinityResidues := GlobalPlace.infinityFibreFinsupp
    (k := k) (F := F) sourceResidues
  let baseAffine := Finsupp.mapDomain
    (IsDedekindDomain.HeightOneSpectrum.under (R k)) affineResidues
  let traceResidues := Differential.globalSimplePoleResidue
    (k := k) (F := RatFunc k) traceOmega htraceGlobal
  let traceByOption := Finsupp.equivMapDomain
    (GlobalPlace.rationalPlaceEquiv (k := k)).symm traceResidues
  have hatAdic (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
      traceByOption (some p) = baseAffine p := by
    obtain ⟨htrace, hresidue⟩ :=
      functionFieldDifferentialTrace_simplePoleTraceResidue_eq_affineMapDomain
        (k := k) (F := F) omega homega p
    change Differential.globalSimplePoleResidue
        (k := k) (F := RatFunc k) traceOmega htraceGlobal
          (GlobalPlace.rationalAdic p) = baseAffine p
    rw [Differential.globalSimplePoleResidue_apply]
    exact hresidue
  have hatInfinity : traceByOption none =
      infinityResidues.sum (fun _ residue => residue) := by
    obtain ⟨htrace, hresidue⟩ :=
      functionFieldDifferentialTrace_simplePoleTraceResidue_eq_infinityFibreSum
        (k := k) (F := F) omega homega
    change Differential.globalSimplePoleResidue
        (k := k) (F := RatFunc k) traceOmega htraceGlobal
          (GlobalPlace.rationalInfinity k) = _
    rw [Differential.globalSimplePoleResidue_apply]
    exact hresidue
  have hsome : traceByOption.some = baseAffine := by
    ext p
    exact hatAdic p
  have hbaseSum :
      baseAffine.sum (fun _ residue => residue) =
        affineResidues.sum (fun _ residue => residue) := by
    exact
      (Finsupp.sum_mapDomain_index_addMonoidHom
        (s := affineResidues)
        (f := IsDedekindDomain.HeightOneSpectrum.under (R k))
        (fun _ => AddMonoidHom.id k))
  have hoptionSum :
      traceByOption.sum (fun _ residue => residue) =
        traceByOption none +
          traceByOption.some.sum (fun _ residue => residue) := by
    exact Finsupp.sum_option_index traceByOption
      (fun _ residue => residue) (fun _ => rfl) (fun _ _ _ => rfl)
  have hsourceSplit :
      sourceResidues.sum (fun _ residue => residue) =
        affineResidues.sum (fun _ residue => residue) +
          infinityResidues.sum (fun _ residue => residue) := by
    exact GlobalPlace.finsupp_sum_eq_affine_add_infinityFibre sourceResidues
  change sourceResidues.sum (fun _ residue => residue) =
    traceResidues.sum (fun _ residue => residue)
  calc
    sourceResidues.sum (fun _ residue => residue) =
        affineResidues.sum (fun _ residue => residue) +
          infinityResidues.sum (fun _ residue => residue) := hsourceSplit
    _ = baseAffine.sum (fun _ residue => residue) +
          infinityResidues.sum (fun _ residue => residue) := by rw [hbaseSum]
    _ = infinityResidues.sum (fun _ residue => residue) +
          baseAffine.sum (fun _ residue => residue) := add_comm _ _
    _ = traceByOption none +
          traceByOption.some.sum (fun _ residue => residue) := by
      rw [hatInfinity, hsome]
    _ = traceByOption.sum (fun _ residue => residue) := hoptionSum.symm
    _ = traceResidues.sum (fun _ residue => residue) := by
      simpa only [traceByOption] using
        (Finsupp.sum_equivMapDomain
          (GlobalPlace.rationalPlaceEquiv (k := k)).symm traceResidues
          (fun _ residue => residue))
end QEC.Coding.AlgebraicGeometry.FunctionFieldGlobalResidue
namespace QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] functionFieldGlobalResidue_Algebra_2
attribute [local instance] functionFieldGlobalResidue_ScalarTower_2
end QEC.Coding.AlgebraicGeometry.Differential
end

set_option autoImplicit false
open scoped BigOperators Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential.functionFieldGlobalResidue_Algebra_2
attribute [local instance] functionFieldGlobalResidue_Algebra_2
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential.functionFieldGlobalResidue_ScalarTower_2
attribute [local instance] functionFieldGlobalResidue_ScalarTower_2
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (omega : Differential k F)
    (homega : IsGlobalSimplePole (k := k) (F := F) omega) :
    globalSimplePoleResidueSum (k := k) (F := F) omega homega = 0 := by
  let traceOmega := functionFieldDifferentialTrace (k := k) (F := F) omega
  let htraceGlobal : IsGlobalSimplePole
      (k := k) (F := RatFunc k) traceOmega :=
    FunctionFieldGlobalResidue.functionFieldDifferentialTrace_isGlobalSimplePole
      (k := k) (F := F) omega homega
  calc
    globalSimplePoleResidueSum (k := k) (F := F) omega homega =
        globalSimplePoleResidueSum (k := k) (F := RatFunc k)
          traceOmega htraceGlobal := by
      exact
        FunctionFieldGlobalResidue.globalSimplePoleResidueSum_eq_traceResidueSum
          (k := k) (F := F) omega homega
    _ = 0 := by
      let f := functionFieldDifferentialCoordinate
        (k := k) (F := RatFunc k) traceOmega
      have htraceAsScalar : traceOmega =
          f • functionFieldDifferentialGenerator
            (k := k) (F := RatFunc k) :=
        functionFieldDifferential_eq_coordinate_smul_generator
          (k := k) (F := RatFunc k) traceOmega
      by_cases hf : f = 0
      · have htraceZero : traceOmega = 0 := by
          rw [htraceAsScalar, hf, zero_smul]
        simpa only [htraceZero] using
          (globalSimplePoleResidueSum_zero (k := k) (F := RatFunc k))
      · have hscalarGlobal : IsGlobalSimplePole
            (k := k) (F := RatFunc k)
            (f • functionFieldDifferentialGenerator
              (k := k) (F := RatFunc k)) := by
          simpa only [← htraceAsScalar] using htraceGlobal
        simpa only [← htraceAsScalar] using
          (globalSimplePoleResidueSum_ratFunc
            (k := k) f hf hscalarGlobal)
end QEC.Coding.AlgebraicGeometry.Differential
