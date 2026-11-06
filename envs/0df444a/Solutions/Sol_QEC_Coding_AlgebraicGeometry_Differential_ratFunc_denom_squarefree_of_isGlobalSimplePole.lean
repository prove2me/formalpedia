-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.ratFunc_denom_squarefree_of_isGlobalSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:49:49.651728+00:00
-- url     : https://prove2.me/submissions/42919345-864a-4f5a-9a5c-5127406ff1ca

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_rationalAdic_order_ge_neg_one_of_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
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



set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    Squarefree f.denom := by
  refine (squarefree_iff_no_irreducibles (RatFunc.denom_ne_zero f)).mpr ?_
  intro q hq hqSqDvd
  have hqPrime : Prime q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hspanIsPrime : (Ideal.span ({q} : Set k[X])).IsPrime :=
    (Ideal.span_singleton_prime hq.ne_zero).mpr hqPrime
  have hspanNe : Ideal.span ({q} : Set k[X]) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hq.ne_zero
  have hspanPrime : Prime (Ideal.span ({q} : Set k[X])) :=
    Ideal.prime_of_isPrime hspanNe hspanIsPrime
  let p : IsDedekindDomain.HeightOneSpectrum k[X] :=
    IsDedekindDomain.HeightOneSpectrum.ofPrime hspanPrime
  let P : GlobalPlace k (RatFunc k) := GlobalPlace.rationalAdic p
  have hdenIntValuation :
      p.intValuation f.denom ≤ WithZero.exp (-(2 : ℤ)) := by
    apply (p.intValuation_le_pow_iff_mem f.denom 2).mpr
    change f.denom ∈ (Ideal.span ({q} : Set k[X])) ^ 2
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simpa only [pow_two] using hqSqDvd
  have hdenIntValuationNe : p.intValuation f.denom ≠ 0 :=
    p.intValuation_ne_zero f.denom (RatFunc.denom_ne_zero f)
  have hdenLog : WithZero.log (p.intValuation f.denom) ≤ -2 := by
    rw [← WithZero.log_exp (-2 : ℤ)]
    exact (WithZero.log_le_log hdenIntValuationNe WithZero.exp_ne_zero).mpr
      hdenIntValuation
  have hdenOrder :
      2 ≤ P.order (algebraMap k[X] (RatFunc k) f.denom) := by
    change 2 ≤ -WithZero.log
      ((p.valuation (RatFunc k))
        (algebraMap k[X] (RatFunc k) f.denom))
    rw [p.valuation_of_algebraMap]
    omega
  have hqDvdDenom : q ∣ f.denom := by
    exact (dvd_mul_right q q).trans hqSqDvd
  have hqNotDvdNum : ¬q ∣ f.num := by
    intro hqDvdNum
    exact hq.not_isUnit
      ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd'
        hqDvdNum hqDvdDenom)
  have hnumNotMem : f.num ∉ p.asIdeal := by
    change f.num ∉ Ideal.span ({q} : Set k[X])
    rw [Ideal.mem_span_singleton]
    exact hqNotDvdNum
  have hnumValuation :
      P.valuation (algebraMap k[X] (RatFunc k) f.num) = 1 := by
    change (p.valuation (RatFunc k))
      (algebraMap k[X] (RatFunc k) f.num) = 1
    exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr hnumNotMem
  have hnumOrder :
      P.order (algebraMap k[X] (RatFunc k) f.num) = 0 := by
    unfold P GlobalPlace.order
    rw [hnumValuation]
    simp
  have hnumMapNe : algebraMap k[X] (RatFunc k) f.num ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hf)
  have hdenMapNe : algebraMap k[X] (RatFunc k) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have horderEq :
      P.order f =
        P.order (algebraMap k[X] (RatFunc k) f.num) -
          P.order (algebraMap k[X] (RatFunc k) f.denom) := by
    calc
      P.order f = P.order
          (algebraMap k[X] (RatFunc k) f.num /
            algebraMap k[X] (RatFunc k) f.denom) :=
        congrArg P.order (RatFunc.num_div_denom f).symm
      _ = P.order (algebraMap k[X] (RatFunc k) f.num) -
          P.order (algebraMap k[X] (RatFunc k) f.denom) := by
        rw [div_eq_mul_inv,
          P.order_mul hnumMapNe (inv_ne_zero hdenMapNe), P.order_inv]
        ring
  have horderLe : P.order f ≤ -2 := by
    rw [horderEq, hnumOrder]
    omega
  have horderGe : -1 ≤ P.order f :=
    rationalAdic_order_ge_neg_one_of_isGlobalSimplePole f hf homega p
  omega
end QEC.Coding.AlgebraicGeometry.Differential
