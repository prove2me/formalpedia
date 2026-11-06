-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_rationalInfinitySimpleFraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:45:58.979974+00:00
-- url     : https://prove2.me/submissions/264196a0-24a1-413e-ac2a-b0886dda8961

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_neg
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalInfinity_residueDegree_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_neg_intDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
private theorem coe_rationalInfinitySimpleFractionCoefficient
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    ((rationalInfinitySimpleFractionCoefficient q b hq hb :
      (GlobalPlace.rationalInfinity k).valuationRing) : RatFunc k) =
      -(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q)) :=
  rfl
omit [Finite k] in
private theorem rationalInfinitySimpleFractionRemainder_degree_lt
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    let c := -b.coeff (q.natDegree - 1)
    let r := -(Polynomial.X * b) - q * Polynomial.C c
    r.degree < q.degree := by
  dsimp only
  by_cases hb0 : b = 0
  · subst b
    simpa using hb
  have hq0 : q ≠ 0 := hq.ne_zero
  have hdegree : b.natDegree < q.natDegree :=
    (Polynomial.natDegree_lt_iff_degree_lt hb0).mpr (by
      simpa only [Polynomial.degree_eq_natDegree hq0] using hb)
  have hsucc_le : b.natDegree + 1 ≤ q.natDegree := Nat.succ_le_of_lt hdegree
  rcases hsucc_le.eq_or_lt with hboundary | hstrict
  · have hindex : q.natDegree - 1 = b.natDegree := by omega
    have hc : -b.coeff (q.natDegree - 1) = -(b.leadingCoeff) := by
      rw [hindex, Polynomial.coeff_natDegree]
    have hp0 : -(Polynomial.X * b) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero Polynomial.X_ne_zero hb0)
    have hdegree_p : (-(Polynomial.X * b)).degree = q.degree := by
      rw [Polynomial.degree_neg, Polynomial.degree_eq_natDegree
        (mul_ne_zero Polynomial.X_ne_zero hb0),
        Polynomial.natDegree_X_mul hb0,
        Polynomial.degree_eq_natDegree hq0, hboundary]
    have hdegree_scaled :
        (q * Polynomial.C (-b.coeff (q.natDegree - 1))).degree = q.degree := by
      rw [Polynomial.degree_mul_C]
      rw [hc]
      exact neg_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hb0)
    have hleading :
        (-(Polynomial.X * b)).leadingCoeff =
          (q * Polynomial.C (-b.coeff (q.natDegree - 1))).leadingCoeff := by
      rw [Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_X, one_mul, Polynomial.leadingCoeff_mul,
        hq.leadingCoeff, one_mul, Polynomial.leadingCoeff_C, hc]
    have hdrop := Polynomial.degree_sub_lt
      (hdegree_p.trans hdegree_scaled.symm) hp0 hleading
    simpa only [hdegree_p] using hdrop
  · have hindex : b.natDegree < q.natDegree - 1 := by omega
    have hcoeff : b.coeff (q.natDegree - 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hindex
    simp only [hcoeff, neg_zero, Polynomial.C_0, mul_zero, sub_zero,
      Polynomial.degree_neg]
    rw [Polynomial.degree_eq_natDegree (mul_ne_zero Polynomial.X_ne_zero hb0),
      Polynomial.natDegree_X_mul hb0, Polynomial.degree_eq_natDegree hq0]
    exact WithBot.coe_lt_coe.mpr hstrict
private theorem rationalInfinity_order_inverseX :
    (GlobalPlace.rationalInfinity k).order (RatFunc.X : RatFunc k)⁻¹ = 1 := by
  rw [GlobalPlace.order_inv,
    RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
      k RatFunc.X RatFunc.X_ne_zero,
    RatFunc.intDegree_X]
  norm_num
private theorem rationalInfinityResidue_simpleFractionCoefficient
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    let c := -b.coeff (q.natDegree - 1)
    (GlobalPlace.rationalInfinity k).residue
        (rationalInfinitySimpleFractionCoefficient q b hq hb) =
      GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k) c := by
  classical
  dsimp only
  let P := GlobalPlace.rationalInfinity k
  let c : k := -b.coeff (q.natDegree - 1)
  let r : k[X] := -(Polynomial.X * b) - q * Polynomial.C c
  have hq0 : q ≠ 0 := hq.ne_zero
  have hq_map : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq0
  have hr_degree : r.degree < q.degree := by
    exact rationalInfinitySimpleFractionRemainder_degree_lt q b hq hb
  have hdiff :
      ((rationalInfinitySimpleFractionCoefficient q b hq hb :
        P.valuationRing) : RatFunc k) - algebraMap k (RatFunc k) c =
        algebraMap k[X] (RatFunc k) r /
          algebraMap k[X] (RatFunc k) q := by
    rw [coe_rationalInfinitySimpleFractionCoefficient]
    change -(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q)) -
        algebraMap k[X] (RatFunc k) (Polynomial.C c) =
      algebraMap k[X] (RatFunc k)
          (-(Polynomial.X * b) - q * Polynomial.C c) /
        algebraMap k[X] (RatFunc k) q
    simp only [map_sub, map_neg, map_mul, RatFunc.algebraMap_X]
    field_simp [hq_map]
  let w : P.valuationRing :=
    rationalInfinitySimpleFractionCoefficient q b hq hb -
      GlobalPlace.constantsToValuationRing P c
  have hw : w ∈ IsLocalRing.maximalIdeal P.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    change P.valuation
      (((rationalInfinitySimpleFractionCoefficient q b hq hb :
        P.valuationRing) : RatFunc k) - algebraMap k (RatFunc k) c) < 1
    rw [hdiff]
    by_cases hr : r = 0
    · simp [hr]
    · have hr_map : algebraMap k[X] (RatFunc k) r ≠ 0 :=
        RatFunc.algebraMap_ne_zero hr
      have hquotient :
          algebraMap k[X] (RatFunc k) r /
              algebraMap k[X] (RatFunc k) q ≠ 0 :=
        div_ne_zero hr_map hq_map
      change RatFunc.inftyValuation k
        (algebraMap k[X] (RatFunc k) r /
          algebraMap k[X] (RatFunc k) q) < 1
      rw [RatFunc.inftyValuation_apply,
        RatFunc.inftyValuation_of_nonzero (F := k) hquotient,
        ← WithZero.exp_zero]
      apply WithZero.exp_lt_exp.mpr
      rw [RatFunc.intDegree_div hr_map hq_map,
        RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
      have hr_natDegree : r.natDegree < q.natDegree :=
        (Polynomial.natDegree_lt_iff_degree_lt hr).mpr (by
          simpa only [Polynomial.degree_eq_natDegree hq0] using hr_degree)
      omega
  change P.residue (rationalInfinitySimpleFractionCoefficient q b hq hb) =
    P.residue (GlobalPlace.constantsToValuationRing P c)
  rw [← sub_eq_zero, ← map_sub]
  exact (P.residue_eq_zero_iff w).mpr hw
private theorem simplePoleResidue_rationalInfinitySimpleFraction
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb) =
      GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k)
        (-b.coeff (q.natDegree - 1)) := by
  unfold rationalInfinitySimpleFractionAtSimplePole
  rw [simplePoleResidue_smul,
    simplePoleResidue_logarithmicDifferential,
    rationalInfinity_order_inverseX]
  simp only [Int.cast_one, mul_one]
  exact rationalInfinityResidue_simpleFractionCoefficient q b hq hb
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    simplePoleTraceResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb :
          Differential k (RatFunc k))
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb).property =
      -b.coeff (q.natDegree - 1) := by
  let P := GlobalPlace.rationalInfinity k
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    GlobalPlace.residueField_finiteDimensional P
  change Algebra.trace k P.residueField
      (simplePoleResidue (k := k) (F := RatFunc k) P
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb)) = _
  rw [simplePoleResidue_rationalInfinitySimpleFraction]
  change Algebra.trace k P.residueField
      (algebraMap k P.residueField (-b.coeff (q.natDegree - 1))) = _
  rw [Algebra.trace_algebraMap,
    ← GlobalPlace.residueDegree_eq_finrank P,
    GlobalPlace.rationalInfinity_residueDegree_eq_one]
  simp
end QEC.Coding.AlgebraicGeometry.Differential
