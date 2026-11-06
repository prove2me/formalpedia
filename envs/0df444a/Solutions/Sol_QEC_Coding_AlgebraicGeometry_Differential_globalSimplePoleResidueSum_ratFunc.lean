-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:53:36.32241+00:00
-- url     : https://prove2.me/submissions/cec633c8-3105-4fd7-9135-0a4663d47000

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimpleFractionGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SquarefreePartialFraction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_GlobalResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSimpleFractionAtSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_exists_ratFunc_eq_sum_simpleFractions_of_squarefree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_finset_sum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_rationalAdicSimpleFraction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_ratFunc_denom_squarefree_of_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_ratFunc_num_degree_lt_denom_degree_of_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_monic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open scoped BigOperators Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
private theorem rationalAdicPolynomial_rationalPlaceOfIrreducible
    (q : k[X]) (hqMonic : q.Monic) (hq : Irreducible q) :
    GlobalPlace.rationalAdicPolynomial
        (rationalPlaceOfIrreducible q hq) = q := by
  apply Polynomial.eq_of_monic_of_associated
    (GlobalPlace.rationalAdicPolynomial_monic
      (rationalPlaceOfIrreducible q hq)) hqMonic
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← GlobalPlace.rationalAdic_asIdeal_eq_span]
  rfl
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped BigOperators Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole (k := k) (F := RatFunc k)
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    globalSimplePoleResidueSum (k := k) (F := RatFunc k)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        homega = 0 := by
  classical
  have hdegree : f.num.degree < f.denom.degree :=
    ratFunc_num_degree_lt_denom_degree_of_isGlobalSimplePole f hf homega
  have hsquarefree : Squarefree f.denom :=
    ratFunc_denom_squarefree_of_isGlobalSimplePole f hf homega
  obtain ⟨s, r, hdata, hfSum⟩ :=
    exists_ratFunc_eq_sum_simpleFractions_of_squarefree
      f hdegree hsquarefree
  let place (q : k[X]) (hq : q ∈ s) :
      IsDedekindDomain.HeightOneSpectrum k[X] :=
    rationalPlaceOfIrreducible q (hdata q hq).2.1
  let term (q : k[X]) : Differential k (RatFunc k) :=
    if hq : q ∈ s then
      ((rationalAdicSimpleFractionAtSimplePole (place q hq) (r q) :
        simplePoleDifferentialLattice
          (GlobalPlace.rationalAdic (place q hq))) :
            Differential k (RatFunc k))
    else 0
  have hplacePolynomial (q : k[X]) (hq : q ∈ s) :
      GlobalPlace.rationalAdicPolynomial (place q hq) = q := by
    exact rationalAdicPolynomial_rationalPlaceOfIrreducible
      q (hdata q hq).1 (hdata q hq).2.1
  have hterm (q : k[X]) (hq : q ∈ s) :
      term q =
        (algebraMap k[X] (RatFunc k) (r q) /
          algebraMap k[X] (RatFunc k) q) •
            functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
    simp only [term, dif_pos hq,
      coe_rationalAdicSimpleFractionAtSimplePole]
    rw [hplacePolynomial q hq]
  have htermSimple (q : k[X]) :
      IsGlobalSimplePole (k := k) (F := RatFunc k) (term q) := by
    by_cases hq : q ∈ s
    · simpa only [term, dif_pos hq] using
        (rationalAdicSimpleFraction_isGlobalSimplePole
          (place q hq) (r q) (by
            rw [hplacePolynomial q hq]
            exact (hdata q hq).2.2))
    · simpa only [term, dif_neg hq] using
        (isGlobalSimplePole_zero (k := k) (F := RatFunc k))
  have htermResidue (q : k[X]) :
      globalSimplePoleResidueSum (k := k) (F := RatFunc k)
          (term q) (htermSimple q) = 0 := by
    by_cases hq : q ∈ s
    · simpa only [term, dif_pos hq] using
        (globalSimplePoleResidueSum_rationalAdicSimpleFraction
          (place q hq) (r q) (by
            rw [hplacePolynomial q hq]
            exact (hdata q hq).2.2))
    · simpa only [term, dif_neg hq] using
        (globalSimplePoleResidueSum_zero (k := k) (F := RatFunc k))
  have hsumDifferential :
      f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) =
        ∑ q ∈ s, term q := by
    calc
      f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) =
          (∑ q ∈ s,
            algebraMap k[X] (RatFunc k) (r q) /
              algebraMap k[X] (RatFunc k) q) •
                functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
            rw [← hfSum]
      _ = ∑ q ∈ s,
          (algebraMap k[X] (RatFunc k) (r q) /
            algebraMap k[X] (RatFunc k) q) •
              functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
            rw [Finset.sum_smul]
      _ = ∑ q ∈ s, term q := by
            apply Finset.sum_congr rfl
            intro q hq
            exact (hterm q hq).symm
  have hsumResidue :
      globalSimplePoleResidueSum (k := k) (F := RatFunc k)
          (∑ q ∈ s, term q)
          (IsGlobalSimplePole.finset_sum s term htermSimple) = 0 := by
    calc
      globalSimplePoleResidueSum (k := k) (F := RatFunc k)
          (∑ q ∈ s, term q)
          (IsGlobalSimplePole.finset_sum s term htermSimple) =
          ∑ q ∈ s, globalSimplePoleResidueSum (k := k) (F := RatFunc k)
            (term q) (htermSimple q) :=
        globalSimplePoleResidueSum_finset_sum s term htermSimple
      _ = 0 := Finset.sum_eq_zero (fun q _ => htermResidue q)
  simpa only [hsumDifferential] using hsumResidue
end QEC.Coding.AlgebraicGeometry.Differential
