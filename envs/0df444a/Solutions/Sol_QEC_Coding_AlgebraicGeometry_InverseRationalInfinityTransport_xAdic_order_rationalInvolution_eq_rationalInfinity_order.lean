-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.xAdic_order_rationalInvolution_eq_rationalInfinity_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:31:01.779209+00:00
-- url     : https://prove2.me/submissions/5e6b6544-35c4-4d28-9f28-afd5db2c512a

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Norm.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X

section
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped LaurentPolynomial Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
private theorem inverseLaurent_eval_eq_involution (p : k[X]) :
    directLaurentToRatFunc k (inverseLaurentCoordinate k p) =
      InverseAffinePlace.rationalInvolution k
        (algebraMap k[X] (RatFunc k) p) := by
  change ((directLaurentToRatFunc k).comp
    (inverseLaurentCoordinate k).toRingHom) p =
      rationalInvolutionOnPolynomial k p
  have hhom : (directLaurentToRatFunc k).comp
      (inverseLaurentCoordinate k).toRingHom =
      rationalInvolutionOnPolynomial k := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [directLaurentToRatFunc, inverseLaurentCoordinate,
        rationalInvolutionOnPolynomial,
        show RatFunc.C c = algebraMap k (RatFunc k) c from rfl,
        (InverseAffinePlace.rationalInvolution k).commutes c]
    · simpa [directLaurentToRatFunc, inverseLaurentCoordinate,
        rationalInvolutionOnPolynomial] using
        (InverseAffinePlace.rationalInvolution_X k).symm
  exact DFunLike.congr_fun hhom p
private theorem involution_polynomial_eq_reverse_div_X_pow (p : k[X]) :
    InverseAffinePlace.rationalInvolution k
        (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.reverse /
        RatFunc.X ^ p.natDegree := by
  rw [← inverseLaurent_eval_eq_involution]
  change LaurentPolynomial.eval₂ (algebraMap k (RatFunc k))
      (Units.mk0 RatFunc.X RatFunc.X_ne_zero)
      ((LaurentPolynomial.invert (R := k)) (Polynomial.toLaurent p)) = _
  apply (eq_div_iff (pow_ne_zero _ RatFunc.X_ne_zero)).mpr
  calc
    directLaurentToRatFunc k
        ((LaurentPolynomial.invert (R := k)) (Polynomial.toLaurent p)) *
        RatFunc.X ^ p.natDegree =
        directLaurentToRatFunc k
          ((LaurentPolynomial.invert (R := k)) (Polynomial.toLaurent p) *
            LaurentPolynomial.T p.natDegree) := by
      rw [map_mul]
      simp [directLaurentToRatFunc]
    _ = directLaurentToRatFunc k (Polynomial.toLaurent p.reverse) := by
      rw [LaurentPolynomial.toLaurent_reverse]
    _ = algebraMap k[X] (RatFunc k) p.reverse := by
      simp only [directLaurentToRatFunc, LaurentPolynomial.eval₂_toLaurent]
      rw [← Polynomial.aeval_def]
      exact RatFunc.aeval_X_left_eq_algebraMap p.reverse
private theorem xAdic_order_polynomial (p : k[X]) (hp : p ≠ 0) :
    GlobalPlace.order (xAdicPlace k)
      (algebraMap k[X] (RatFunc k) p) = (p.natTrailingDegree : Int) := by
  classical
  letI : StrongNormalizationMonoid k := UniqueFactorizationMonoid.strongNormalizationMonoid
  unfold xAdicPlace GlobalPlace.order
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg]
  · rw [WithZero.log_exp]
    simp only [neg_neg]
    congr 1
    rw [Ideal.count_associates_factors_eq
      (by simpa [Ideal.zero_eq_bot] using hp)
      (Polynomial.idealX k).isPrime (Polynomial.idealX k).ne_bot]
    rw [Polynomial.idealX_span,
      Ideal.count_span_normalizedFactors_eq_of_normUnit hp
        Polynomial.normUnit_X Polynomial.prime_X]
    rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree',
      Polynomial.rootMultiplicity_eq_multiplicity, if_neg hp]
    have hX : (Polynomial.X - Polynomial.C (0 : k) : k[X]) = Polynomial.X := by
      simp
    rw [hX]
    symm
    simpa only [← Polynomial.X_eq_normalize] using
      (UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
        Polynomial.irreducible_X hp)
  · exact hp
private theorem xAdic_order_involution_polynomial (p : k[X]) (hp : p ≠ 0) :
    GlobalPlace.order (xAdicPlace k)
      (InverseAffinePlace.rationalInvolution k
        (algebraMap k[X] (RatFunc k) p)) = -(p.natDegree : Int) := by
  have hX : GlobalPlace.order (xAdicPlace k) RatFunc.X = 1 := by
    simpa using
      (xAdic_order_polynomial k (Polynomial.X : k[X]) (by simp))
  have hXpow (n : ℕ) :
      GlobalPlace.order (xAdicPlace k) (RatFunc.X ^ n) = (n : Int) := by
    induction n with
    | zero => simp [GlobalPlace.order]
    | succ n hn =>
        rw [pow_succ,
          GlobalPlace.order_mul _ (pow_ne_zero _ RatFunc.X_ne_zero) RatFunc.X_ne_zero,
          hn, hX]
        push_cast
        ring
  rw [involution_polynomial_eq_reverse_div_X_pow,
    div_eq_mul_inv, GlobalPlace.order_mul]
  · rw [xAdic_order_polynomial]
    · rw [GlobalPlace.order_inv]
      rw [hXpow, Polynomial.natTrailingDegree_reverse]
      ring
    · exact (Polynomial.reverse_eq_zero.not).mpr hp
  · exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr
      ((Polynomial.reverse_eq_zero.not).mpr hp)
  · exact inv_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero)
private theorem xAdic_order_involution_eq_neg_intDegree
    (h : RatFunc k) (hh : h ≠ 0) :
    GlobalPlace.order (xAdicPlace k)
      (InverseAffinePlace.rationalInvolution k h) = -h.intDegree := by
  induction h using RatFunc.induction_on with
  | f p q hq =>
      have hpq : algebraMap k[X] (RatFunc k) p /
          algebraMap k[X] (RatFunc k) q ≠ 0 := by
        simpa [RatFunc.mk_eq_div] using hh
      have hp : p ≠ 0 := by
        intro hp
        apply hpq
        simp [hp]
      have hqmap : algebraMap k[X] (RatFunc k) q ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hq
      have hpmap : algebraMap k[X] (RatFunc k) p ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hp
      rw [map_div₀, div_eq_mul_inv, GlobalPlace.order_mul]
      · rw [GlobalPlace.order_inv,
          xAdic_order_involution_polynomial k p hp,
          xAdic_order_involution_polynomial k q hq]
        rw [RatFunc.intDegree_div]
        · rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
          ring
        · exact hpmap
        · exact hqmap
      · exact (map_ne_zero_iff _ (InverseAffinePlace.rationalInvolution k).injective).mpr hpmap
      · exact inv_ne_zero
          ((map_ne_zero_iff _ (InverseAffinePlace.rationalInvolution k).injective).mpr hqmap)
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped LaurentPolynomial Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
theorem _root_.solution
    (h : RatFunc k) :
    GlobalPlace.order (xAdicPlace k)
      (InverseAffinePlace.rationalInvolution k h) =
      GlobalPlace.order (GlobalPlace.rationalInfinity k) h := by
  by_cases hh : h = 0
  · simp [hh, xAdicPlace, GlobalPlace.order]
  classical
  rw [xAdic_order_involution_eq_neg_intDegree k h hh]
  unfold GlobalPlace.rationalInfinity GlobalPlace.order
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero (F := k) hh,
    WithZero.log_exp]
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
