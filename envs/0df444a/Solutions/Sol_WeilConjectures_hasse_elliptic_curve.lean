-- Prove2me | solution 1 for WeilConjectures.hasse_elliptic_curve
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T15:29:01.572195+00:00
-- url     : https://prove2.me/submissions/2c24adb0-baa6-46b9-8d07-a147e0cd24cc

import Mathlib
import Definitions.Def_WeilConjectures_RiemannRochFLT
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Mathlib.RingTheory.PowerSeries.Derivative
import Theorems.Thm_AlgebraicCurve_exists_LPolynomial_of_finite
import Theorems.Thm_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
import Theorems.Thm_AlgebraicCurve_norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_WeierstrassCurve_Affine_Chart_infinity_heightOne_unique
import Theorems.Thm_WeilConjectures_Bridge_genusFF_eq_one_of_isElliptic
import Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/
set_option linter.style.haveILetI false
section
section
open Polynomial
open scoped Polynomial.Bivariate RatFunc nonZeroDivisors
noncomputable section
namespace WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k)
namespace CoordinateRing
end CoordinateRing
theorem derivative_polynomial :
    derivative W.polynomial = W.polynomialY := by
  rw [polynomial, polynomialY]
  simp only [derivative_sub, derivative_add, derivative_pow, derivative_X, derivative_C,
    derivative_C_mul, mul_one, map_ofNat, map_natCast]
  ring
theorem polynomialY_ne_zero [W.IsElliptic] : W.polynomialY ≠ 0 := by
  intro h
  rw [polynomialY] at h
  have h1 : (C (2 : k) : k[X]) = 0 := by
    simpa using congr_arg (fun p => Polynomial.coeff p 1) h
  have h0 : (C W.a₁ * X + C W.a₃ : k[X]) = 0 := by
    simpa using congr_arg (fun p => Polynomial.coeff p 0) h
  have h2 : (2 : k) = 0 := Polynomial.C_eq_zero.mp h1
  have ha₁ : W.a₁ = 0 := by
    simpa using congr_arg (fun p => Polynomial.coeff p 1) h0
  have ha₃ : W.a₃ = 0 := by
    simpa using congr_arg (fun p => Polynomial.coeff p 0) h0
  have hΔ : W.Δ = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₁, ha₃]
    linear_combination (-32 * W.a₂ ^ 3 * W.a₆ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 32 * W.a₄ ^ 3
      - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2
  exact not_isUnit_zero (hΔ ▸ W.isUnit_Δ)
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
omit [IsFractionRing W.CoordinateRing K] in
theorem algebraPolynomial_isScalarTower :
    letI := W.algebraPolynomial K
    IsScalarTower k[X] W.CoordinateRing K :=
  letI := W.algebraPolynomial K
  IsScalarTower.of_algebraMap_eq fun _ => rfl
section AbstractPolynomialAlgebra
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
theorem algebraRatFunc_isScalarTower :
    letI := W.algebraRatFunc K
    IsScalarTower k[X] k⟮X⟯ K := by
  letI := W.algebraRatFunc K
  refine IsScalarTower.of_algebraMap_eq fun p => ?_
  exact (IsFractionRing.lift_algebraMap (W.algebraMap_polynomial_injective K) p).symm
section AbstractRatFuncAlgebra
variable [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
include W in
theorem functionField : _root_.FunctionField k K :=
  Module.Finite.of_basis (W.basisRatFunc K)
omit [IsFractionRing W.CoordinateRing K] in
theorem aeval_yCoord :
    Polynomial.aeval (W.yCoord K) (W.polynomial.map (algebraMap k[X] k⟮X⟯)) = 0 := by
  have h1 : eval₂ (algebraMap k[X] K) (W.yCoord K) W.polynomial = 0 := by
    rw [IsScalarTower.algebraMap_eq k[X] W.CoordinateRing K, yCoord]
    show eval₂ ((algebraMap W.CoordinateRing K).comp (AdjoinRoot.of W.polynomial))
      ((algebraMap W.CoordinateRing K) (AdjoinRoot.root W.polynomial)) W.polynomial = 0
    rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq k[X] k⟮X⟯ K]
  exact h1
omit [IsFractionRing W.CoordinateRing K] in
theorem yCoord_isIntegral : _root_.IsIntegral k⟮X⟯ (W.yCoord K) :=
  ⟨W.polynomial.map (algebraMap k[X] k⟮X⟯), monic_polynomial.map _, by
    rw [← Polynomial.aeval_def]; exact W.aeval_yCoord K⟩
theorem minpoly_yCoord :
    minpoly k⟮X⟯ (W.yCoord K) = W.polynomial.map (algebraMap k[X] k⟮X⟯) := by
  have hmonic : (W.polynomial.map (algebraMap k[X] k⟮X⟯)).Monic := monic_polynomial.map _
  have hdvd : minpoly k⟮X⟯ (W.yCoord K) ∣ W.polynomial.map (algebraMap k[X] k⟮X⟯) :=
    minpoly.dvd k⟮X⟯ (W.yCoord K) (W.aeval_yCoord K)
  have hdeg : (W.polynomial.map (algebraMap k[X] k⟮X⟯)).natDegree = 2 := by
    rw [monic_polynomial.natDegree_map, natDegree_polynomial]
  have hle : (minpoly k⟮X⟯ (W.yCoord K)).natDegree ≤ 2 := by
    rw [← hdeg]; exact natDegree_le_of_dvd hdvd hmonic.ne_zero
  have hge : 2 ≤ (minpoly k⟮X⟯ (W.yCoord K)).natDegree := by
    rcases Nat.lt_or_ge (minpoly k⟮X⟯ (W.yCoord K)).natDegree 2 with hlt | hge
    · have hpos := minpoly.natDegree_pos (W.yCoord_isIntegral K)
      have h1 : (minpoly k⟮X⟯ (W.yCoord K)).natDegree = 1 := by omega
      exact absurd (minpoly.natDegree_eq_one_iff.mp h1) (W.yCoord_notMem_range K)
    · exact hge
  have heq : (minpoly k⟮X⟯ (W.yCoord K)).natDegree = 2 := le_antisymm hle hge
  obtain ⟨c, hc⟩ := hdvd
  have hmp : (minpoly k⟮X⟯ (W.yCoord K)).Monic := minpoly.monic (W.yCoord_isIntegral K)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hmonic.ne_zero hc
  have hcdeg : c.natDegree = 0 := by
    have := congr_arg Polynomial.natDegree hc
    rw [hdeg, Polynomial.natDegree_mul hmp.ne_zero hc0, heq] at this
    omega
  have hcC : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hcdeg
  have hlead : c.coeff 0 = 1 := by
    have := congr_arg Polynomial.leadingCoeff hc
    rw [hmonic.leadingCoeff, Polynomial.leadingCoeff_mul, hmp.leadingCoeff, one_mul,
      hcC, Polynomial.leadingCoeff_C] at this
    exact this.symm
  rw [hc, hcC, hlead, Polynomial.C_1, mul_one]
include W in
set_option synthInstance.maxHeartbeats 200000 in
theorem isSeparable [W.IsElliptic] : Algebra.IsSeparable k⟮X⟯ K := by
  have hsep : IsSeparable k⟮X⟯ (W.yCoord K) := by
    rw [IsSeparable, separable_iff_derivative_ne_zero
      (minpoly.irreducible (W.yCoord_isIntegral K)), minpoly_yCoord, Polynomial.derivative_map,
      derivative_polynomial]
    intro hzero
    rw [Polynomial.map_eq_zero_iff (IsFractionRing.injective k[X] k⟮X⟯)] at hzero
    exact W.polynomialY_ne_zero hzero
  have htop : IntermediateField.adjoin k⟮X⟯ {W.yCoord K} = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span k⟮X⟯ (Set.range (W.basisRatFunc K)) := by
      rw [(W.basisRatFunc K).span_eq]; trivial
    have hle : Submodule.span k⟮X⟯ (Set.range (W.basisRatFunc K)) ≤
        Subalgebra.toSubmodule (IntermediateField.adjoin k⟮X⟯ {W.yCoord K}).toSubalgebra := by
      rw [Submodule.span_le, Set.range_subset_iff]
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule, basisRatFunc_zero]
        exact one_mem _
      · simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule, basisRatFunc_one]
        exact IntermediateField.mem_adjoin_simple_self k⟮X⟯ (W.yCoord K)
    exact hle hz
  haveI : Algebra.IsSeparable k⟮X⟯ (IntermediateField.adjoin k⟮X⟯ {W.yCoord K}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k⟮X⟯ K).mpr hsep
  exact AlgEquiv.Algebra.isSeparable
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
end AbstractRatFuncAlgebra
end AbstractPolynomialAlgebra
end WeierstrassCurve.Affine
namespace FunctionField
open scoped Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k[X] K]
end FunctionField
theorem FunctionField.isFullConstantField_of_isAlgClosed (k K : Type*) [Field k] [Field K]
    [Algebra k K] [IsAlgClosed k] : FunctionField.IsFullConstantField k K where
  algebraic_mem x hx := by
    have hint : _root_.IsIntegral k x := hx.isIntegral
    have hlead : (minpoly k x).leadingCoeff = 1 := minpoly.monic hint
    have hdeg : (minpoly k x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    have h0 : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
    rw [eq_X_add_C_of_degree_eq_one hdeg, hlead, Polynomial.C_1, one_mul, map_add,
      Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at h0
    exact ⟨-(minpoly k x).coeff 0, by rw [map_neg, ← h0]⟩
end
end
end
section
section
open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc
namespace WeierstrassCurve.Affine.Chart
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
lemma maximal_eq_XYIdeal [IsAlgClosed k] (I : Ideal W.CoordinateRing) [I.IsMaximal] :
    ∃ x y : k, ∃ _ : W.Nonsingular x y,
      I = CoordinateRing.XYIdeal W x (Polynomial.C y) := by
  let L := W.CoordinateRing ⧸ I
  letI : Field L := Ideal.Quotient.field I
  haveI : Algebra.FiniteType k L := Algebra.FiniteType.quotient k I
  haveI : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  haveI : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  obtain ⟨x, hx⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    (Ideal.Quotient.mk I (CoordinateRing.mk W (Polynomial.C Polynomial.X)))
  obtain ⟨y, hy⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    (Ideal.Quotient.mk I (CoordinateRing.mk W Polynomial.X))
  have heq : W.Equation x y := by
    apply (W.map_equation (algebraMap k L).injective x y).mp
    rw [hx, hy]
    simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map] using
      (coordinate_equation W).map (Ideal.Quotient.mk I)
  have hns : W.Nonsingular x y := W.equation_iff_nonsingular.mp heq
  have hle : CoordinateRing.XYIdeal W x (Polynomial.C y) ≤ I := by
    rw [CoordinateRing.XYIdeal, Ideal.span_le]
    rintro z (rfl | hz)
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [CoordinateRing.XClass, map_sub]
      rw [sub_eq_zero]
      change (Ideal.Quotient.mk I) (CoordinateRing.mk W (Polynomial.C Polynomial.X)) =
        algebraMap k L x
      exact hx.symm
    · have : z = CoordinateRing.YClass W (Polynomial.C y) := by simpa using hz
      subst z
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [CoordinateRing.YClass, map_sub]
      rw [sub_eq_zero]
      change (Ideal.Quotient.mk I) (CoordinateRing.mk W Polynomial.X) =
        algebraMap k L y
      exact hy.symm
  refine ⟨x, y, hns, ?_⟩
  exact ((XYIdeal_isMaximal W hns).eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hle).symm
include W in
theorem place_dichotomy [IsAlgClosed k] (v : PlaceA k K) :
    (∃ P : W.Point, v = placeOfPoint W K P) ∨ v = infinityPlace K := by
  rcases v with v | v
  · let e := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (coordinateRingEquivIntegers W K).toRingEquiv
    let u := e.symm v
    letI : u.asIdeal.IsMaximal := u.isPrime.isMaximal u.ne_bot
    obtain ⟨x, y, h, hu⟩ := maximal_eq_XYIdeal W u.asIdeal
    have hueq : u = affineHeightOne W h := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact hu
    left
    refine ⟨.some x y h, ?_⟩
    change Sum.inl v = Sum.inl (e (affineHeightOne W h))
    congr 1
    rw [← hueq, Equiv.apply_symm_apply]
  · right
    exact congrArg Sum.inr
      (infinity_heightOne_unique W K v (infinityHeightOne (k := k) K))
end WeierstrassCurve.Affine.Chart
end
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped WithZero
open MonoidWithZeroHom
noncomputable section
namespace WeilConjectures.Bridge
section Valuations
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace FLTPlace
variable (v : AlgebraicCurve.Place k K)
end FLTPlace
end Valuations
section Places
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}
end Places
section Divisors
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}
end Divisors
section Hypotheses
open scoped Polynomial RatFunc IntermediateField
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] WeilConjectures.Bridge.instIsScalarTowerRatFunc
theorem isCurveOver : AlgebraicCurve.IsCurveOver k K :=
  AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k K (xK k K) (transcendental_xK k K)
    inferInstance inferInstance
theorem essFiniteType : Algebra.EssFiniteType k K := by
  have : Algebra.EssFiniteType k[X] k⟮X⟯ :=
    Algebra.EssFiniteType.of_isLocalization k⟮X⟯ (nonZeroDivisors k[X])
  have : Algebra.EssFiniteType k k⟮X⟯ := Algebra.EssFiniteType.comp k k[X] k⟮X⟯
  exact Algebra.EssFiniteType.comp k k⟮X⟯ K
end Hypotheses
section Genus
open scoped Polynomial RatFunc
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [FunctionField.IsFullConstantField k K]
end Genus
section Weierstrass
open scoped Polynomial RatFunc
variable {k : Type*} [Field k] [PerfectField k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
  (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
  [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [FunctionField.IsFullConstantField k K]
end Weierstrass
end WeilConjectures.Bridge
end
end
section
namespace PowerSeries
variable {R : Type*} [CommRing R] [IsAddTorsionFree R]
theorem coeff_eq_of_derivative_eq_mul {N : ℕ} {f g a b : R⟦X⟧}
    (hf : derivative R f = f * a) (hg : derivative R g = g * b)
    (h0 : constantCoeff f = constantCoeff g)
    (hab : ∀ j, j + 1 < N → coeff j a = coeff j b) :
    ∀ m, m < N → coeff m f = coeff m g := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    cases m with
    | zero => simpa only [coeff_zero_eq_constantCoeff] using h0
    | succ n =>
      have e1 := congrArg (coeff n) hf
      have e2 := congrArg (coeff n) hg
      rw [coeff_derivative, coeff_mul] at e1 e2
      have equ : coeff (n + 1) f * (n + 1) = coeff (n + 1) g * (n + 1) := by
        rw [e1, e2]
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, j⟩ hij
        have hsum : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        rw [ih i (by omega) (by omega), hab j (by omega)]
      rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul,
        mul_comm, ← nsmul_eq_mul] at equ
      exact (smul_right_inj (Nat.succ_ne_zero n)).mp equ
theorem eq_of_derivative_eq_mul {f g a : R⟦X⟧}
    (hf : derivative R f = f * a) (hg : derivative R g = g * a)
    (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext m
  exact coeff_eq_of_derivative_eq_mul (N := m + 1) hf hg h0
    (fun _ _ => rfl) m (Nat.lt_succ_self m)
end PowerSeries
end
section
noncomputable section
open PowerSeries
namespace WeilConjectures.Bridge
def countingSeries (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m ↦ (N (m + 1) : ℚ)
@[simp]
theorem coeff_countingSeries (N : ℕ → ℕ) (m : ℕ) :
    coeff m (countingSeries N) = (N (m + 1) : ℚ) := by
  simp [countingSeries]
def IsZetaSeries (N : ℕ → ℕ) (Z : ℚ⟦X⟧) : Prop :=
  constantCoeff Z = 1 ∧ d⁄dX ℚ Z = countingSeries N * Z
theorem IsZetaSeries.unique {N : ℕ → ℕ} {Z W : ℚ⟦X⟧}
    (hZ : IsZetaSeries N Z) (hW : IsZetaSeries N W) : Z = W :=
  PowerSeries.eq_of_derivative_eq_mul
    (by rw [hZ.2, mul_comm]) (by rw [hW.2, mul_comm]) (hZ.1.trans hW.1.symm)
def zetaLog (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m ↦ if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ)
theorem zetaOfCounts_eq (N : ℕ → ℕ) :
    zetaOfCounts N = (PowerSeries.exp ℚ).subst (zetaLog N) := rfl
@[simp]
theorem constantCoeff_zetaLog (N : ℕ → ℕ) : constantCoeff (zetaLog N) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, zetaLog, coeff_mk]
  simp
theorem hasSubst_zetaLog (N : ℕ → ℕ) : HasSubst (zetaLog N) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_zetaLog N)
theorem derivative_zetaLog (N : ℕ → ℕ) : d⁄dX ℚ (zetaLog N) = countingSeries N := by
  ext m
  rw [coeff_derivative, zetaLog, coeff_mk, coeff_countingSeries]
  have hne : (m : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
  push_cast
  field_simp
theorem constantCoeff_zetaOfCounts (N : ℕ → ℕ) : constantCoeff (zetaOfCounts N) = 1 := by
  rw [zetaOfCounts_eq, ← coeff_zero_eq_constantCoeff_apply,
    coeff_subst' (hasSubst_zetaLog N), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [he, constantCoeff_zetaLog]
theorem derivative_zetaOfCounts (N : ℕ → ℕ) :
    d⁄dX ℚ (zetaOfCounts N) = countingSeries N * zetaOfCounts N := by
  rw [zetaOfCounts_eq, derivative_subst (hasSubst_zetaLog N), derivative_exp,
    derivative_zetaLog, mul_comm]
theorem zetaOfCounts_isZetaSeries (N : ℕ → ℕ) : IsZetaSeries N (zetaOfCounts N) :=
  ⟨constantCoeff_zetaOfCounts N, derivative_zetaOfCounts N⟩
theorem IsZetaSeries.eq_zetaOfCounts {N : ℕ → ℕ} {Z : ℚ⟦X⟧} (hZ : IsZetaSeries N Z) :
    Z = zetaOfCounts N :=
  hZ.unique (zetaOfCounts_isZetaSeries N)
end WeilConjectures.Bridge
end
end
section
open PowerSeries
namespace WeilConjectures.Bridge
section Field
variable {K : Type*} [Field K]
def powerSumSeries (s : Multiset K) : K⟦X⟧ :=
  PowerSeries.mk fun m ↦ (s.map (· ^ (m + 1))).sum
@[simp]
theorem coeff_powerSumSeries (s : Multiset K) (m : ℕ) :
    coeff m (powerSumSeries s) = (s.map (· ^ (m + 1))).sum := by
  simp [powerSumSeries]
theorem powerSumSeries_zero : powerSumSeries (0 : Multiset K) = 0 := by
  ext
  simp
theorem powerSumSeries_cons (a : K) (s : Multiset K) :
    powerSumSeries (a ::ₘ s) = PowerSeries.mk (fun m ↦ a ^ (m + 1)) + powerSumSeries s := by
  ext
  simp
theorem mk_pow_succ_mul_one_sub (a : K) :
    PowerSeries.mk (fun m ↦ a ^ (m + 1)) * (1 - C a * X) = C a := by
  have h : PowerSeries.mk (fun m ↦ a ^ (m + 1)) = C a * rescale a (PowerSeries.mk 1) := by
    ext n
    simp [coeff_rescale, pow_succ, mul_comm]
  rw [h, ← rescale_X, mul_assoc]
  have hsub : (1 : K⟦X⟧) - rescale a X = rescale a (1 - X) := by
    rw [map_sub, map_one]
  rw [hsub, ← map_mul, mk_one_mul_one_sub_eq_one, map_one, mul_one]
noncomputable def oneSubProd (s : Multiset K) : K⟦X⟧ :=
  (s.map fun a ↦ (1 - C a * X : K⟦X⟧)).prod
theorem constantCoeff_oneSubProd (s : Multiset K) : constantCoeff (oneSubProd s) = 1 := by
  rw [oneSubProd, map_multiset_prod, Multiset.map_map]
  simp
theorem oneSubProd_ne_zero (s : Multiset K) : oneSubProd s ≠ 0 := by
  intro h
  simpa [h] using constantCoeff_oneSubProd s
theorem derivative_oneSubProd (s : Multiset K) :
    d⁄dX K (oneSubProd s) = -(powerSumSeries s * oneSubProd s) := by
  induction s using Multiset.induction_on with
  | empty => simp [oneSubProd, powerSumSeries_zero]
  | cons a s ih =>
    simp only [oneSubProd] at ih ⊢
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, ih, powerSumSeries_cons]
    have hd : d⁄dX K (1 - C a * X : K⟦X⟧) = -C a := by
      rw [map_sub, Derivation.leibniz, derivative_C, derivative_X]
      simp
    rw [hd, smul_eq_mul, smul_eq_mul]
    linear_combination (s.map fun a ↦ (1 - C a * X : K⟦X⟧)).prod * mk_pow_succ_mul_one_sub a
theorem eq_powerSumSeries_sub {Z c : K⟦X⟧} (hZ' : d⁄dX K Z = c * Z) {α β : Multiset K}
    (h : Z * oneSubProd β = oneSubProd α) :
    c = powerSumSeries β - powerSumSeries α := by
  have hd := congrArg (d⁄dX K) h
  rw [Derivation.leibniz, derivative_oneSubProd, derivative_oneSubProd, hZ', smul_eq_mul,
    smul_eq_mul] at hd
  have hz : (c - powerSumSeries β + powerSumSeries α) * (Z * oneSubProd β) = 0 := by
    linear_combination hd + powerSumSeries α * h
  rw [h] at hz
  have := (mul_eq_zero.mp hz).resolve_right (oneSubProd_ne_zero α)
  linear_combination this
end Field
section Map
variable {R S : Type*} [CommRing R] [CommRing S]
theorem derivative_map (f : R →+* S) (φ : R⟦X⟧) :
    d⁄dX S (PowerSeries.map f φ) = PowerSeries.map f (d⁄dX R φ) := by
  ext n
  simp [coeff_derivative]
end Map
theorem cast_count_eq_of_map_zetaOfCounts_mul {K : Type*} [Field K] [CharZero K] (N : ℕ → ℕ)
    {α β : Multiset K}
    (h : PowerSeries.map (algebraMap ℚ K) (zetaOfCounts N) * oneSubProd β = oneSubProd α)
    {m : ℕ} (hm : 0 < m) :
    (N m : K) = (β.map (· ^ m)).sum - (α.map (· ^ m)).sum := by
  have hZ' : d⁄dX K (PowerSeries.map (algebraMap ℚ K) (zetaOfCounts N)) =
      PowerSeries.map (algebraMap ℚ K) (countingSeries N) *
        PowerSeries.map (algebraMap ℚ K) (zetaOfCounts N) := by
    rw [derivative_map, derivative_zetaOfCounts, map_mul]
  have hc := congrArg (coeff (m - 1)) (eq_powerSumSeries_sub hZ' h)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm.ne'
  simpa using hc
end WeilConjectures.Bridge
end
section
open Polynomial
namespace WeilConjectures.Bridge
section Reverse
variable {R S : Type*} [Semiring R] [Semiring S]
theorem reverse_map_of_injective (f : R →+* S) (hf : Function.Injective f) (p : R[X]) :
    (p.map f).reverse = p.reverse.map f := by
  ext n
  simp [coeff_reverse, coeff_map, natDegree_map_eq_of_injective hf]
theorem reverse_reverse_of_coeff_zero_ne_zero {p : R[X]} (h : p.coeff 0 ≠ 0) :
    p.reverse.reverse = p := by
  have ht : p.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr h)
  have hd : p.reverse.natDegree = p.natDegree := by
    rw [reverse_natDegree, ht, Nat.sub_zero]
  ext n
  rw [coeff_reverse, hd, coeff_reverse, revAt_invol]
theorem reverse_one' : (1 : R[X]).reverse = 1 := by
  ext n
  rw [coeff_reverse, natDegree_one]
  rcases n with _ | n <;> simp [revAt]
end Reverse
section Field
variable {K : Type*} [Field K]
theorem reverse_X_sub_C (a : K) : (X - C a).reverse = 1 - C a * X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_C]
  have hX : reflect 1 (X : K[X]) = 1 := by
    have := reflect_monomial (R := K) 1 1
    rwa [pow_one, revAt_le le_rfl, Nat.sub_self, pow_zero] at this
  rw [hX, pow_one]
theorem reverse_multiset_prod (s : Multiset K[X]) :
    s.prod.reverse = (s.map reverse).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse_one']
  | cons a s ih => rw [Multiset.prod_cons, reverse_mul_of_domain, ih, Multiset.map_cons,
      Multiset.prod_cons]
theorem monic_reverse_of_coeff_zero_eq_one {p : K[X]} (h0 : p.coeff 0 = 1) : p.reverse.Monic := by
  rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by simp [h0]), h0]
theorem eq_prod_one_sub_C_mul_X [IsAlgClosed K] {p : K[X]} (h0 : p.coeff 0 = 1) :
    p = (p.reverse.roots.map fun a ↦ 1 - C a * X).prod := by
  have hsplit : (p.reverse.roots.map fun a ↦ X - C a).prod = p.reverse :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_reverse_of_coeff_zero_eq_one h0)
      IsAlgClosed.card_roots_eq_natDegree
  conv_lhs => rw [← reverse_reverse_of_coeff_zero_ne_zero (p := p) (by simp [h0]), ← hsplit]
  rw [reverse_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun a _ ↦ reverse_X_sub_C a
end Field
section FunctionalEquation
variable {K : Type*} [Field K] {p : K[X]} {q : K} {g : ℕ}
theorem natDegree_eq_of_symm (hq : q ≠ 0) (h0 : p.coeff 0 = 1) (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) :
    p.natDegree = 2 * g := by
  refine le_antisymm hdeg (le_natDegree_of_ne_zero ?_)
  have := hsymm 0 (Nat.zero_le _)
  rw [Nat.sub_zero, pow_zero, mul_one, h0, mul_one] at this
  rw [this]
  exact pow_ne_zero _ hq
end FunctionalEquation
end WeilConjectures.Bridge
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace WeilConjectures.Bridge
section FunctionField
variable (k F₀ : Type*) [Field k] [Finite k] [Field F₀] [Algebra k F₀]
  [AlgebraicCurve.IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
noncomputable abbrev effCount (n : ℕ) : ℕ :=
  Nat.card {D : AlgebraicCurve.Divisor k F₀ //
    0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)}
noncomputable abbrev placeCount (m : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors m, d * Nat.card {v : AlgebraicCurve.Place k F₀ | v.deg = d}
theorem zetaOfCounts_eq_mk_effCount {N : ℕ → ℕ} (hN : ∀ m, 0 < m → N m = placeCount k F₀ m)
    (hA0 : effCount k F₀ 0 = 1) :
    zetaOfCounts N = PowerSeries.mk fun n ↦ (effCount k F₀ n : ℚ) := by
  refine (IsZetaSeries.eq_zetaOfCounts ⟨?_, ?_⟩).symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hA0,
      Nat.cast_one]
  · ext n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_countingSeries, PowerSeries.coeff_mk]
    have h := AlgebraicCurve.card_effectiveDivisors_mul_eq_sum k F₀ (n + 1)
    have h' : (n + 1) * effCount k F₀ (n + 1) =
        ∑ i ∈ Finset.range (n + 1), N (i + 1) * effCount k F₀ (n - i) := by
      have hI : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) := by
        ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [h, hI, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by simp) fun i hi ↦ ?_
      rw [hN (i + 1) (Nat.succ_pos i), add_comm 1 i,
        show n + 1 - (i + 1) = n - i by omega]
    exact_mod_cast (mul_comm _ _).trans h'
end FunctionField
section Main
theorem coe_oneSubProd {K : Type*} [Field K] (s : Multiset K) :
    (((s.map fun a ↦ 1 - C a * X).prod : K[X]) : PowerSeries K) = oneSubProd s := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map,
    oneSubProd]
  congr 1
  refine Multiset.map_congr rfl fun a _ ↦ ?_
  simp [Polynomial.coeToPowerSeries.ringHom_apply]
end Main
end WeilConjectures.Bridge
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace WeilConjectures.Bridge
theorem lPolynomial_of_functionField
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    {N : ℕ → ℕ} (hN : ∀ m, 0 < m → N m = placeCount k F₀ m) :
    AlgebraicCurve.genusFF k F₀ = AlgebraicCurve.genusFF K F ∧
    ∃ L : ℤ[X],
      L.natDegree = 2 * AlgebraicCurve.genusFF K F ∧
      L.coeff 0 = 1 ∧
      (∀ i ≤ 2 * AlgebraicCurve.genusFF K F,
        L.coeff (2 * AlgebraicCurve.genusFF K F - i) * (Nat.card k : ℤ) ^ i =
          (Nat.card k : ℤ) ^ AlgebraicCurve.genusFF K F * L.coeff i) ∧
      zetaOfCounts N *
          (((1 - X : ℤ[X]).map (Int.castRingHom ℚ) : PowerSeries ℚ) *
            ((1 - C (Nat.card k : ℤ) * X : ℤ[X]).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        (L.map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      (∀ a ∈ (L.map (Int.castRingHom ℂ)).reverse.roots,
        ‖a‖ = Real.sqrt (Nat.card k)) ∧
      (∀ m, 0 < m → (N m : ℂ) = (Nat.card k : ℂ) ^ m + 1 -
        (((L.map (Int.castRingHom ℂ)).reverse.roots.map fun a ↦ a ^ m).sum)) := by
  have hC := AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card k K F₀ F hfg hgen
    φ hφ
  obtain ⟨L, hLdeg, hL0, hLsymm, hLser⟩ := AlgebraicCurve.exists_LPolynomial_of_finite k F₀ hC
  have hgenus := AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
    k K F₀ F hfg hgen φ hφ hC
  set g := AlgebraicCurve.genusFF k F₀ with hg
  set q := Nat.card k with hq
  have hq0 : 0 < q := Nat.card_pos
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hA0 : effCount k F₀ 0 = 1 := by
    have := congrArg (PowerSeries.coeff 0) hLser
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_sub, map_one,
      PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, mul_zero, sub_zero, one_mul,
      Polynomial.constantCoeff_coe, hL0] at this
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk] at this
    exact_mod_cast this
  have hZ := zetaOfCounts_eq_mk_effCount k F₀ hN hA0
  have hrat : zetaOfCounts N *
      (((1 - X : ℤ[X]).map (Int.castRingHom ℚ) : PowerSeries ℚ) *
        ((1 - C (q : ℤ) * X : ℤ[X]).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
      (L.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
    have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hLser
    rw [Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe,
      Polynomial.polynomial_map_coe, ← h, hZ]
    simp only [map_mul, map_sub, map_one, PowerSeries.map_X, PowerSeries.map_C,
      Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, Polynomial.coe_mul,
      Polynomial.coe_C]
    have hmk : PowerSeries.map (Int.castRingHom ℚ)
        (PowerSeries.mk fun n ↦ (effCount k F₀ n : ℤ)) =
        PowerSeries.mk fun n ↦ (effCount k F₀ n : ℚ) := by
      ext n
      simp
    rw [hmk]
    simp only [eq_intCast, Int.cast_natCast]
    ring
  set Lc := L.map (Int.castRingHom ℂ) with hLc
  have hLc0 : Lc.coeff 0 = 1 := by simp [Lc, coeff_map, hL0]
  have hLcdeg : Lc.natDegree ≤ 2 * g := natDegree_map_le.trans hLdeg
  have hLcsymm : ∀ i ≤ 2 * g, Lc.coeff (2 * g - i) * (q : ℂ) ^ i = (q : ℂ) ^ g * Lc.coeff i := by
    intro i hi
    have := congrArg (Int.cast : ℤ → ℂ) (hLsymm i hi)
    push_cast at this
    simpa [Lc, coeff_map] using this
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hLnat : L.natDegree = 2 * g := by
    rw [← natDegree_map_eq_of_injective hinj]
    exact natDegree_eq_of_symm hqC hLc0 hLcdeg hLcsymm
  set α₁ := Lc.reverse.roots with hα₁
  have hfac : Lc = (α₁.map fun a ↦ 1 - C a * X).prod := eq_prod_one_sub_C_mul_X hLc0
  have hprod : PowerSeries.map (algebraMap ℚ ℂ) (zetaOfCounts N) * oneSubProd {1, (q : ℂ)} =
      oneSubProd α₁ := by
    have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hrat
    rw [map_mul] at h
    rw [← coe_oneSubProd α₁, ← hfac]
    convert h using 2
    · simp only [oneSubProd, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton, map_one, one_mul]
      simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, Polynomial.map_mul,
        Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X,
        Polynomial.coe_mul, map_mul, map_sub, map_one, PowerSeries.map_X,
        Polynomial.map_natCast, map_natCast]
      have hc : ((q : ℚ[X]) : PowerSeries ℚ) = (q : PowerSeries ℚ) := by
        rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_natCast]
      rw [hc, map_natCast]
    · rw [hLc, Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe,
        ← RingHom.comp_apply, ← PowerSeries.map_comp]
      congr 2
  have hcount : ∀ m, 0 < m → (N m : ℂ) = (q : ℂ) ^ m + 1 - ((α₁.map fun a ↦ a ^ m).sum) := by
    intro m hm
    rw [cast_count_eq_of_map_zetaOfCounts_mul N hprod hm]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, one_pow]
    ring
  have hPmonic : L.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by simp [hL0]), hL0]
  have hLt : L.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr (by simp [hL0]))
  have hdegP : L.reverse.natDegree = 2 * AlgebraicCurve.genusFF K F := by
    rw [reverse_natDegree, hLt, Nat.sub_zero, hLnat, hgenus]
  have h0P : L.reverse.coeff 0 = (q : ℤ) ^ AlgebraicCurve.genusFF K F := by
    have := hLsymm 0 (Nat.zero_le _)
    rw [Nat.sub_zero, pow_zero, mul_one, hL0, mul_one] at this
    rw [coeff_zero_reverse, leadingCoeff, hLnat, this, hgenus]
  have hrootsP : (L.reverse.map (Int.castRingHom ℂ)).roots = α₁ := by
    rw [← reverse_map_of_injective _ hinj]
  have hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints
          (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (q : ℂ) ^ n + 1 -
          (((L.reverse.map (Int.castRingHom ℂ)).roots.map fun z ↦ z ^ n).sum) := by
    intro n hn
    rw [(AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
      k K F₀ F hfg hgen φ hφi hφ n hn).2, ← placeCount, ← hN n hn, hcount n hn, hrootsP]
  have hRH := AlgebraicCurve.norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
    k K F₀ F hfg hgen φ hφi hφ L.reverse hPmonic hdegP h0P hfix
  rw [hrootsP] at hRH
  refine ⟨hgenus.symm, L, hLnat.trans (by rw [hgenus]), hL0, ?_, hrat, hRH, hcount⟩
  rw [hgenus]
  exact hLsymm
end WeilConjectures.Bridge
end
section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open Polynomial FiniteField
noncomputable section
namespace WeilConjectures.Bridge
section Integral
theorem isIntegralElem_inv_of_field {A B : Type*} [Field A] [Field B] (f : A →+* B) {x : B}
    (hx : f.IsIntegralElem x) : f.IsIntegralElem x⁻¹ := by
  let := f.toAlgebra
  exact IsIntegral.inv (R := A) hx
theorem isIntegralElem_of_apply_eq_pow {A : Type*} [CommRing A] (f : A →+* A) {x : A} {n : ℕ}
    (hn : 0 < n) (h : f x = x ^ n) : f.IsIntegralElem x :=
  ⟨X ^ n - C x, monic_X_pow_sub_C x hn.ne', by simp [eval₂_sub, h]⟩
end Integral
section Induction
variable {A : Type*} [CommRing A] (P : A[X][X])
theorem adjoinRoot_induction {M : AdjoinRoot P → Prop}
    (hconst : ∀ a : A, M (AdjoinRoot.of P (Polynomial.C a)))
    (hX : M (AdjoinRoot.of P Polynomial.X)) (hY : M (AdjoinRoot.root P))
    (hadd : ∀ x y, M x → M y → M (x + y)) (hmul : ∀ x y, M x → M y → M (x * y))
    (r : AdjoinRoot P) : M r := by
  have hof : ∀ c : A[X], M (AdjoinRoot.of P c) := by
    intro c
    induction c using Polynomial.induction_on with
    | C a => exact hconst a
    | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact hmul _ _ h hX
  induction r using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C a => rw [AdjoinRoot.mk_C]; exact hof a
    | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      exact hmul _ _ h hY
end Induction
section Frobenius
variable {k K : Type*} [Field k] [Fintype k] [Field K] [Algebra k K]
  (P : k[X][X]) (Q : K[X][X]) (hQ : Q = P.map (mapRingHom (algebraMap k K)))
def adjoinRootBaseChange : AdjoinRoot P →+* AdjoinRoot Q :=
  AdjoinRoot.map (mapRingHom (algebraMap k K)) P Q (by rw [hQ])
theorem adjoinRootBaseChange_comp_of :
    (adjoinRootBaseChange P Q hQ).comp (AdjoinRoot.of P) =
      (AdjoinRoot.of Q).comp (mapRingHom (algebraMap k K)) :=
  RingHom.ext fun _ => by simp [adjoinRootBaseChange]
@[simp]
theorem adjoinRootBaseChange_of (c : k[X]) :
    adjoinRootBaseChange P Q hQ (AdjoinRoot.of P c) =
      AdjoinRoot.of Q (c.map (algebraMap k K)) := by
  simp [adjoinRootBaseChange]
@[simp]
theorem adjoinRootBaseChange_root :
    adjoinRootBaseChange P Q hQ (AdjoinRoot.root P) = AdjoinRoot.root Q := by
  simp [adjoinRootBaseChange]
theorem adjoinRootBaseChange_mk (p : k[X][X]) :
    adjoinRootBaseChange P Q hQ (AdjoinRoot.mk P p) =
      AdjoinRoot.mk Q (p.map (mapRingHom (algebraMap k K))) := by
  have : (adjoinRootBaseChange P Q hQ).comp (AdjoinRoot.mk P) =
      (AdjoinRoot.mk Q).comp (mapRingHom (mapRingHom (algebraMap k K))) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [AdjoinRoot.mk_C]
    · simp [AdjoinRoot.mk_X]
  exact RingHom.congr_fun this p
theorem adjoinRootBaseChange_injective (hP : P.Monic) :
    Function.Injective (adjoinRootBaseChange P Q hQ) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p', rfl⟩ := AdjoinRoot.mk_surjective r
  have hmk : AdjoinRoot.mk P (p' %ₘ P) = AdjoinRoot.mk P p' := by
    rw [← AdjoinRoot.modByMonicHom_mk hP]
    exact AdjoinRoot.mk_leftInverse hP _
  rw [← hmk] at hr ⊢
  rw [adjoinRootBaseChange_mk, AdjoinRoot.mk_eq_zero] at hr
  have hinj : Function.Injective (mapRingHom (algebraMap k K)) :=
    Polynomial.map_injective _ (algebraMap k K).injective
  have hQdeg : Q.degree = P.degree := by
    rw [hQ, degree_map_eq_of_injective hinj]
  have hlt : (Polynomial.map (mapRingHom (algebraMap k K)) (p' %ₘ P)).degree < Q.degree := by
    rw [degree_map_eq_of_injective hinj, hQdeg]
    exact degree_modByMonic_lt p' hP
  have h0 := eq_zero_of_dvd_of_degree_lt hr hlt
  rw [Polynomial.map_eq_zero_iff hinj] at h0
  rw [h0, map_zero]
def frobCoeff : K[X] →+* AdjoinRoot Q :=
  (AdjoinRoot.of Q).comp (expand K (Fintype.card k)).toRingHom
theorem frobCoeff_apply (p : K[X]) :
    frobCoeff (k := k) Q p = AdjoinRoot.of Q (expand K (Fintype.card k) p) := rfl
theorem frobCoeff_comp_map :
    (frobCoeff (k := k) Q).comp (mapRingHom (algebraMap k K)) =
      (frobeniusAlgHom k (AdjoinRoot Q)).toRingHom.comp
        ((AdjoinRoot.of Q).comp (mapRingHom (algebraMap k K))) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, frobCoeff_apply, expand_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, frobeniusAlgHom_apply]
    rw [← map_pow, ← Polynomial.C_pow, ← map_pow, FiniteField.pow_card]
  · simp [frobCoeff_apply]
include hQ in
theorem frob_eval₂_eq_zero :
    Q.eval₂ (frobCoeff (k := k) Q) (AdjoinRoot.root Q ^ Fintype.card k) = 0 := by
  have h1 : Q.eval₂ (frobCoeff (k := k) Q) (AdjoinRoot.root Q ^ Fintype.card k) =
      (P.map (mapRingHom (algebraMap k K))).eval₂ (frobCoeff (k := k) Q)
        (AdjoinRoot.root Q ^ Fintype.card k) :=
    congrArg (fun Q' => Q'.eval₂ (frobCoeff (k := k) Q) (AdjoinRoot.root Q ^ Fintype.card k)) hQ
  have h2 : (0 : AdjoinRoot Q) =
      (P.map (mapRingHom (algebraMap k K))).eval₂ (AdjoinRoot.of Q) (AdjoinRoot.root Q) := by
    rw [← congrArg (fun Q' => Q'.eval₂ (AdjoinRoot.of Q) (AdjoinRoot.root Q)) hQ,
      AdjoinRoot.eval₂_root]
  rw [h1, eval₂_map, frobCoeff_comp_map,
    show AdjoinRoot.root Q ^ Fintype.card k =
      (frobeniusAlgHom k (AdjoinRoot Q)).toRingHom (AdjoinRoot.root Q) from rfl,
    ← Polynomial.hom_eval₂, ← eval₂_map, ← h2, map_zero]
def frobAdjoinRoot : AdjoinRoot Q →ₐ[K] AdjoinRoot Q :=
  { AdjoinRoot.lift (frobCoeff (k := k) Q) _ (frob_eval₂_eq_zero P Q hQ) with
    commutes' := fun c => by
      change AdjoinRoot.lift _ _ _ (algebraMap K (AdjoinRoot Q) c) = _
      rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, AdjoinRoot.lift_of, frobCoeff_apply,
        Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, expand_C] }
theorem frobAdjoinRoot_of (p : K[X]) :
    frobAdjoinRoot P Q hQ (AdjoinRoot.of Q p) =
      AdjoinRoot.of Q (expand K (Fintype.card k) p) :=
  AdjoinRoot.lift_of (frob_eval₂_eq_zero P Q hQ)
theorem frobAdjoinRoot_root :
    frobAdjoinRoot P Q hQ (AdjoinRoot.root Q) = AdjoinRoot.root Q ^ Fintype.card k :=
  AdjoinRoot.lift_root (frob_eval₂_eq_zero P Q hQ)
theorem frobAdjoinRoot_comp_of :
    (frobAdjoinRoot P Q hQ).toRingHom.comp (AdjoinRoot.of Q) = frobCoeff (k := k) Q :=
  RingHom.ext fun p => frobAdjoinRoot_of P Q hQ p
theorem frobAdjoinRoot_baseChange (r : AdjoinRoot P) :
    frobAdjoinRoot P Q hQ (adjoinRootBaseChange P Q hQ r) =
      adjoinRootBaseChange P Q hQ r ^ Fintype.card k := by
  have : (frobAdjoinRoot P Q hQ).toRingHom.comp (adjoinRootBaseChange P Q hQ) =
      (frobeniusAlgHom k (AdjoinRoot Q)).toRingHom.comp (adjoinRootBaseChange P Q hQ) := by
    apply AdjoinRoot.ringHom_ext
    · rw [RingHom.comp_assoc, RingHom.comp_assoc, adjoinRootBaseChange_comp_of,
        ← RingHom.comp_assoc, frobAdjoinRoot_comp_of, frobCoeff_comp_map]
    · simp only [RingHom.comp_apply, adjoinRootBaseChange_root, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, frobAdjoinRoot_root, frobeniusAlgHom_apply]
  exact RingHom.congr_fun this r
theorem frobAdjoinRoot_injective [IsDomain (AdjoinRoot Q)] (hmon : Q.Monic)
    (hdeg : 0 < Q.natDegree) : Function.Injective (frobAdjoinRoot P Q hQ) := by
  have : Module.Finite K[X] (AdjoinRoot Q) := (AdjoinRoot.powerBasis' hmon).finite
  have : Algebra.IsIntegral K[X] (AdjoinRoot Q) := Algebra.IsIntegral.of_finite K[X] (AdjoinRoot Q)
  have hcoeff : Function.Injective (frobCoeff (k := k) Q) :=
    (AdjoinRoot.of.injective_of_degree_ne_zero
      (by rw [degree_eq_natDegree hmon.ne_zero]; exact_mod_cast hdeg.ne')).comp
      (expand_injective Fintype.card_pos)
  have hker : RingHom.ker (frobAdjoinRoot P Q hQ).toRingHom = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := K[X])
    rw [RingHom.comap_ker, AdjoinRoot.algebraMap_eq, frobAdjoinRoot_comp_of]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hcoeff
  exact (RingHom.injective_iff_ker_eq_bot _).mpr hker
theorem frobAdjoinRoot_isIntegral : (frobAdjoinRoot P Q hQ).toRingHom.IsIntegral := by
  intro r
  induction r using adjoinRoot_induction with
  | hconst a =>
    have h := (frobAdjoinRoot P Q hQ).toRingHom.isIntegralElem_map (x := AdjoinRoot.of Q (C a))
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, frobAdjoinRoot_of, expand_C] at h
  | hX =>
    refine isIntegralElem_of_apply_eq_pow _ (Fintype.card_pos (α := k)) ?_
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, frobAdjoinRoot_of, expand_X, map_pow]
  | hY =>
    refine isIntegralElem_of_apply_eq_pow _ (Fintype.card_pos (α := k)) ?_
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, frobAdjoinRoot_root]
  | hadd x y hx hy => exact hx.add _ hy
  | hmul x y hx hy => exact hx.mul _ hy
variable (F : Type*) [Field F] [Algebra (AdjoinRoot Q) F] [IsFractionRing (AdjoinRoot Q) F]
  [Algebra K F] [IsScalarTower K (AdjoinRoot Q) F]
include F in
theorem isDomain_adjoinRoot_of_isFractionRing : IsDomain (AdjoinRoot Q) :=
  (IsFractionRing.injective (AdjoinRoot Q) F).isDomain (algebraMap (AdjoinRoot Q) F)
theorem algebraMap_comp_frobAdjoinRoot_injective (hmon : Q.Monic) (hdeg : 0 < Q.natDegree) :
    Function.Injective
      ((IsScalarTower.toAlgHom K (AdjoinRoot Q) F).comp (frobAdjoinRoot P Q hQ)) := by
  have := isDomain_adjoinRoot_of_isFractionRing Q F
  exact (IsFractionRing.injective (AdjoinRoot Q) F).comp
    (frobAdjoinRoot_injective P Q hQ hmon hdeg)
def frobFractionField (hmon : Q.Monic) (hdeg : 0 < Q.natDegree) : F →ₐ[K] F :=
  IsFractionRing.liftAlgHom (algebraMap_comp_frobAdjoinRoot_injective P Q hQ F hmon hdeg)
variable {F}
theorem frobFractionField_algebraMap (hmon : Q.Monic) (hdeg : 0 < Q.natDegree)
    (r : AdjoinRoot Q) :
    frobFractionField P Q hQ F hmon hdeg (algebraMap (AdjoinRoot Q) F r) =
      algebraMap (AdjoinRoot Q) F (frobAdjoinRoot P Q hQ r) := by
  rw [frobFractionField, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl
theorem frobFractionField_isIntegral (hmon : Q.Monic) (hdeg : 0 < Q.natDegree) :
    (frobFractionField P Q hQ F hmon hdeg).toRingHom.IsIntegral := by
  set φ := frobFractionField P Q hQ F hmon hdeg
  have hcomp : φ.toRingHom.comp (algebraMap (AdjoinRoot Q) F) =
      (algebraMap (AdjoinRoot Q) F).comp (frobAdjoinRoot P Q hQ).toRingHom :=
    RingHom.ext fun r => frobFractionField_algebraMap P Q hQ hmon hdeg r
  have hA : ∀ r, φ.toRingHom.IsIntegralElem (algebraMap (AdjoinRoot Q) F r) := by
    intro r
    obtain ⟨p, hpm, hp⟩ := frobAdjoinRoot_isIntegral P Q hQ r
    refine ⟨p.map (algebraMap (AdjoinRoot Q) F), hpm.map _, ?_⟩
    rw [eval₂_map, hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
  intro z
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (AdjoinRoot Q) z
  rw [div_eq_mul_inv]
  exact (hA a).mul _ (isIntegralElem_inv_of_field _ (hA b))
variable (F₀ : Type*) [Field F₀] [Algebra (AdjoinRoot P) F₀] [IsFractionRing (AdjoinRoot P) F₀]
  [Algebra F₀ F]
theorem frobFractionField_apply_algebraMap (hmon : Q.Monic) (hdeg : 0 < Q.natDegree)
    (hcompat : ∀ r, algebraMap F₀ F (algebraMap (AdjoinRoot P) F₀ r) =
      algebraMap (AdjoinRoot Q) F (adjoinRootBaseChange P Q hQ r)) (x : F₀) :
    frobFractionField P Q hQ F hmon hdeg (algebraMap F₀ F x) =
      algebraMap F₀ F (x ^ Nat.card k) := by
  let : Algebra k F := ((algebraMap K F).comp (algebraMap k K)).toAlgebra
  have h : (frobFractionField P Q hQ F hmon hdeg).toRingHom.comp (algebraMap F₀ F) =
      (frobeniusAlgHom k F).toRingHom.comp (algebraMap F₀ F) := by
    apply IsFractionRing.ringHom_ext (A := AdjoinRoot P)
    intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hcompat,
      frobFractionField_algebraMap, frobAdjoinRoot_baseChange, map_pow, frobeniusAlgHom_apply]
  rw [map_pow, Nat.card_eq_fintype_card]
  exact RingHom.congr_fun h x
theorem adjoin_range_algebraMap_eq_top
    (hcompat : ∀ r, algebraMap F₀ F (algebraMap (AdjoinRoot P) F₀ r) =
      algebraMap (AdjoinRoot Q) F (adjoinRootBaseChange P Q hQ r)) :
    IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ := by
  set T := IntermediateField.adjoin K (Set.range (algebraMap F₀ F))
  have himg : ∀ r : AdjoinRoot P,
      algebraMap (AdjoinRoot Q) F (adjoinRootBaseChange P Q hQ r) ∈ T := by
    intro r
    rw [← hcompat]
    exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
  have hR : ∀ r : AdjoinRoot Q, algebraMap (AdjoinRoot Q) F r ∈ T := by
    intro r
    induction r using adjoinRoot_induction with
    | hconst a =>
      rw [← AdjoinRoot.algebraMap_eq, show (C a : K[X]) = algebraMap K K[X] a by simp,
        ← IsScalarTower.algebraMap_apply K K[X] (AdjoinRoot Q),
        ← IsScalarTower.algebraMap_apply K (AdjoinRoot Q) F]
      exact T.algebraMap_mem a
    | hX =>
      have := himg (AdjoinRoot.of P Polynomial.X)
      rwa [adjoinRootBaseChange_of, Polynomial.map_X] at this
    | hY =>
      have := himg (AdjoinRoot.root P)
      rwa [adjoinRootBaseChange_root] at this
    | hadd x y hx hy => rw [map_add]; exact T.add_mem hx hy
    | hmul x y hx hy => rw [map_mul]; exact T.mul_mem hx hy
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (AdjoinRoot Q) z
  exact T.div_mem (hR a) (hR b)
theorem exists_finset_adjoin_eq_top [Algebra k F₀] [IsScalarTower k (AdjoinRoot P) F₀] :
    ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤ := by
  classical
  refine ⟨{algebraMap (AdjoinRoot P) F₀ (AdjoinRoot.of P Polynomial.X),
    algebraMap (AdjoinRoot P) F₀ (AdjoinRoot.root P)}, ?_⟩
  set T := IntermediateField.adjoin k
    (({algebraMap (AdjoinRoot P) F₀ (AdjoinRoot.of P Polynomial.X),
      algebraMap (AdjoinRoot P) F₀ (AdjoinRoot.root P)} : Finset F₀) : Set F₀)
  have hR : ∀ r : AdjoinRoot P, algebraMap (AdjoinRoot P) F₀ r ∈ T := by
    intro r
    induction r using adjoinRoot_induction with
    | hconst a =>
      rw [← AdjoinRoot.algebraMap_eq, show (C a : k[X]) = algebraMap k k[X] a by simp,
        ← IsScalarTower.algebraMap_apply k k[X] (AdjoinRoot P),
        ← IsScalarTower.algebraMap_apply k (AdjoinRoot P) F₀]
      exact T.algebraMap_mem a
    | hX => exact IntermediateField.subset_adjoin _ _ (by simp)
    | hY => exact IntermediateField.subset_adjoin _ _ (by simp)
    | hadd x y hx hy => rw [map_add]; exact T.add_mem hx hy
    | hmul x y hx hy => rw [map_mul]; exact T.mul_mem hx hy
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (AdjoinRoot P) z
  exact T.div_mem (hR a) (hR b)
end Frobenius
end WeilConjectures.Bridge
end
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
open Polynomial FiniteField
open scoped Polynomial.Bivariate
noncomputable section
namespace WeilConjectures.Bridge
section ValuationSubring
variable {F : Type*} [Field F] (V : ValuationSubring F)
theorem valuation_lt_one_of_inv_notMem {z : F} (hz : z⁻¹ ∉ V) : V.valuation z < 1 := by
  by_contra h
  rw [not_lt] at h
  apply hz
  rw [← V.valuation_le_one_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ h
theorem inv_notMem_of_valuation_lt_one {z : F} (hz0 : z ≠ 0) (hz : V.valuation z < 1) :
    z⁻¹ ∉ V := by
  rw [← V.valuation_le_one_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hz0))).mpr hz
theorem pow_notMem_valuationSubring {z : F} (hz : z ∉ V) {n : ℕ} (hn : n ≠ 0) : z ^ n ∉ V := by
  rw [← V.valuation_le_one_iff, not_le] at hz ⊢
  rw [map_pow]
  exact one_lt_pow₀ hz hn
theorem mem_of_inv_sub_notMem {u c : F} (hc : c ∈ V) (h : (u - c)⁻¹ ∉ V) : u ∈ V := by
  have h1 := valuation_lt_one_of_inv_notMem V h
  rw [show u = (u - c) + c by ring]
  exact V.add_mem _ _ ((V.valuation_le_one_iff _).mp h1.le) hc
theorem eq_of_inv_sub_notMem {K : Type*} [Field K] [Algebra K F]
    (hK : ∀ a : K, algebraMap K F a ∈ V) {u : F} {a a' : K}
    (h : (u - algebraMap K F a)⁻¹ ∉ V) (h' : (u - algebraMap K F a')⁻¹ ∉ V) : a = a' := by
  by_contra hne
  have hv := valuation_lt_one_of_inv_notMem V h
  have hv' := valuation_lt_one_of_inv_notMem V h'
  have hd : algebraMap K F (a' - a) = (u - algebraMap K F a) - (u - algebraMap K F a') := by
    rw [map_sub]; ring
  have hlt : V.valuation (algebraMap K F (a' - a)) < 1 := by
    rw [hd]
    exact (V.valuation.map_sub _ _).trans_lt (max_lt hv hv')
  have hne' : a' - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hinv := hK (a' - a)⁻¹
  rw [map_inv₀] at hinv
  exact inv_notMem_of_valuation_lt_one V ((_root_.map_ne_zero _).mpr hne') hlt hinv
end ValuationSubring
section Center
open FunctionField FunctionField.Chart WeierstrassCurve.Affine
open scoped RatFunc
variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]
  (F : Type*) [Field F] [Algebra W.CoordinateRing F] [IsFractionRing W.CoordinateRing F]
  [Algebra K[X] F] [IsScalarTower K[X] W.CoordinateRing F]
  [Algebra K⟮X⟯ F] [IsScalarTower K[X] K⟮X⟯ F]
  [_root_.FunctionField K F] [Algebra.IsSeparable K⟮X⟯ F]
  [Algebra K F] [IsScalarTower K K[X] F] [IsFullConstantField K F]
local instance instCoordinateConstantsTowerHasse : IsScalarTower K W.CoordinateRing F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K K[X] F,
      IsScalarTower.algebraMap_apply K K[X] W.CoordinateRing,
      ← IsScalarTower.algebraMap_apply K[X] W.CoordinateRing F]
abbrev xF : F := algebraMap W.CoordinateRing F (CoordinateRing.mk W (C X))
abbrev yF : F := W.yCoord F
theorem algebraMap_const_eq (a : K) :
    algebraMap K F a = algebraMap W.CoordinateRing F (CoordinateRing.mk W (C (C a))) := by
  rw [IsScalarTower.algebraMap_apply K W.CoordinateRing F]
  rfl
theorem xF_sub_eq (a : K) :
    xF W F - algebraMap K F a = algebraMap W.CoordinateRing F (CoordinateRing.XClass W a) := by
  rw [algebraMap_const_eq W F, CoordinateRing.XClass, ← map_sub, ← map_sub, ← C_sub]
theorem yF_sub_eq (b : K) :
    yF W F - algebraMap K F b =
      algebraMap W.CoordinateRing F (CoordinateRing.YClass W (C b)) := by
  rw [algebraMap_const_eq W F, CoordinateRing.YClass, yF, yCoord, ← map_sub, ← map_sub]
theorem placeOfPoint_some_toValuationSubring {a b : K} (h : W.Nonsingular a b) :
    (placeOfPoint W F (.some a b h)).toValuationSubring =
      ((IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
        (Chart.coordinateRingEquivIntegers W F).toRingEquiv
          (Chart.affineHeightOne W h)).valuation F).valuationSubring := rfl
theorem placeOfPoint_zero_toValuationSubring :
    (placeOfPoint W F 0).toValuationSubring =
      ((Chart.infinityHeightOne (k := K) F).valuation F).valuationSubring := rfl
theorem inv_notMem_placeOfPoint_of_mem {a b : K} (h : W.Nonsingular a b)
    {r : W.CoordinateRing} (hr : r ∈ CoordinateRing.XYIdeal W a (C b)) (hr0 : r ≠ 0) :
    (algebraMap W.CoordinateRing F r)⁻¹ ∉ (placeOfPoint W F (.some a b h)).toValuationSubring := by
  rw [placeOfPoint_some_toValuationSubring]
  set e := Chart.coordinateRingEquivIntegers W F
  set v := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv
    (Chart.affineHeightOne W h)
  have hne : algebraMap W.CoordinateRing F r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing F)).mpr hr0
  have hlt : v.valuation F (algebraMap W.CoordinateRing F r) < 1 := by
    rw [← IsIntegralClosure.algebraMap_equiv K[X] W.CoordinateRing F (ringOfIntegers K F) r]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    change e.toRingEquiv.symm (e r) ∈ (Chart.affineHeightOne W h).asIdeal
    rw [show e.toRingEquiv.symm (e r) = r from e.toRingEquiv.symm_apply_apply r]
    exact hr
  rw [Valuation.mem_valuationSubring_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hne))).mpr hlt
theorem inv_sub_notMem_placeOfPoint {a b : K} (h : W.Nonsingular a b) :
    (xF W F - algebraMap K F a)⁻¹ ∉ (placeOfPoint W F (.some a b h)).toValuationSubring ∧
      (yF W F - algebraMap K F b)⁻¹ ∉ (placeOfPoint W F (.some a b h)).toValuationSubring := by
  constructor
  · rw [xF_sub_eq]
    exact inv_notMem_placeOfPoint_of_mem W F h (Ideal.subset_span (Set.mem_insert _ _))
      (CoordinateRing.XClass_ne_zero (W' := W) a)
  · rw [yF_sub_eq]
    exact inv_notMem_placeOfPoint_of_mem W F h
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)) (CoordinateRing.YClass_ne_zero (W' := W) _)
theorem xF_notMem_placeOfPoint_zero : xF W F ∉ (placeOfPoint W F 0).toValuationSubring := by
  rw [placeOfPoint_zero_toValuationSubring, Valuation.mem_valuationSubring_iff, not_le, xF,
    Chart.xCoord_eq_XK]
  exact Place.infinite_X_gt_one K F _
theorem algebraMap_mem_place (v : Place K F) (a : K) : algebraMap K F a ∈ v.toValuationSubring :=
  v.triv_on_k a
theorem xF_mem_of_inv_sub_notMem {v : Place K F} {a : K}
    (h : (xF W F - algebraMap K F a)⁻¹ ∉ v.toValuationSubring) : xF W F ∈ v.toValuationSubring :=
  mem_of_inv_sub_notMem _ (algebraMap_mem_place F v a) h
theorem placeOfPoint_injective : Function.Injective (placeOfPoint W F) := by
  have hsome_zero : ∀ {a b : K} (h : W.Nonsingular a b),
      placeOfPoint W F (.some a b h) ≠ placeOfPoint W F 0 := by
    intro a b h heq
    apply xF_notMem_placeOfPoint_zero W F
    rw [← heq]
    exact xF_mem_of_inv_sub_notMem W F (inv_sub_notMem_placeOfPoint W F h).1
  rintro (_ | ⟨a, b, h⟩) (_ | ⟨a', b', h'⟩) heq
  · rfl
  · exact absurd heq.symm (hsome_zero h')
  · exact absurd heq (hsome_zero h)
  · have hx := (inv_sub_notMem_placeOfPoint W F h').1
    have hy := (inv_sub_notMem_placeOfPoint W F h').2
    rw [← heq] at hx hy
    obtain rfl := eq_of_inv_sub_notMem _ (algebraMap_mem_place F _)
      (inv_sub_notMem_placeOfPoint W F h).1 hx
    obtain rfl := eq_of_inv_sub_notMem _ (algebraMap_mem_place F _)
      (inv_sub_notMem_placeOfPoint W F h).2 hy
    rfl
theorem exists_eq_placeOfPoint [IsAlgClosed K] (v : Place K F) :
    ∃ P : W.Point, v = placeOfPoint W F P := by
  obtain ⟨w, rfl⟩ := (chartToPlace K F).surjective v
  rcases Chart.place_dichotomy W F w with ⟨P, rfl⟩ | rfl
  · exact ⟨P, rfl⟩
  · exact ⟨0, rfl⟩
def pointPlaceEquiv [IsAlgClosed K] : W.Point ≃ Place K F :=
  Equiv.ofBijective (placeOfPoint W F)
    ⟨placeOfPoint_injective W F, fun v => (exists_eq_placeOfPoint W F v).imp fun _ h => h.symm⟩
theorem eq_placeOfPoint_some [IsAlgClosed K] (v : Place K F) {a b : K} (h : W.Nonsingular a b)
    (hx : (xF W F - algebraMap K F a)⁻¹ ∉ v.toValuationSubring)
    (hy : (yF W F - algebraMap K F b)⁻¹ ∉ v.toValuationSubring) :
    v = placeOfPoint W F (.some a b h) := by
  obtain ⟨P, rfl⟩ := exists_eq_placeOfPoint W F v
  rcases P with _ | ⟨a', b', h'⟩
  · exact absurd (xF_mem_of_inv_sub_notMem W F hx) (xF_notMem_placeOfPoint_zero W F)
  · obtain rfl := eq_of_inv_sub_notMem _ (algebraMap_mem_place F _)
      (inv_sub_notMem_placeOfPoint W F h').1 hx
    obtain rfl := eq_of_inv_sub_notMem _ (algebraMap_mem_place F _)
      (inv_sub_notMem_placeOfPoint W F h').2 hy
    rfl
theorem eq_placeOfPoint_zero [IsAlgClosed K] (v : Place K F)
    (hx : xF W F ∉ v.toValuationSubring) : v = placeOfPoint W F 0 := by
  obtain ⟨P, rfl⟩ := exists_eq_placeOfPoint W F v
  rcases P with _ | ⟨a, b, h⟩
  · rfl
  · exact absurd (xF_mem_of_inv_sub_notMem W F (inv_sub_notMem_placeOfPoint W F h).1) hx
end Center
section Frobenius
open FunctionField WeierstrassCurve.Affine
open scoped RatFunc
variable {k K : Type*} [Field k] [Fintype k] [Field K] [IsAlgClosed K] [Algebra k K]
  [DecidableEq K] (E : WeierstrassCurve k) [E.IsElliptic]
instance instIsEllipticBaseChange : (E.baseChange K).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k K)).IsElliptic
variable (F : Type*) [Field F] [Algebra (E.baseChange K).toAffine.CoordinateRing F] [IsFractionRing (E.baseChange K).toAffine.CoordinateRing F]
  [Algebra K[X] F] [IsScalarTower K[X] (E.baseChange K).toAffine.CoordinateRing F]
  [Algebra K⟮X⟯ F] [IsScalarTower K[X] K⟮X⟯ F]
  [_root_.FunctionField K F] [Algebra.IsSeparable K⟮X⟯ F]
  [Algebra K F] [IsScalarTower K K[X] F] [IsFullConstantField K F]
  (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
  (hφx : φ (xF (E.baseChange K).toAffine F) = xF (E.baseChange K).toAffine F ^ Fintype.card k) (hφy : φ (yF (E.baseChange K).toAffine F) = yF (E.baseChange K).toAffine F ^ Fintype.card k)
def pointFLTPlaceEquiv : (E.baseChange K).toAffine.Point ≃ AlgebraicCurve.Place K F :=
  (pointPlaceEquiv (E.baseChange K).toAffine F).trans (placeEquiv K F)
include hφx hφy in
theorem restrictAlong_pointPlace (P : (E.baseChange K).toAffine.Point) :
    AlgebraicCurve.Place.restrictAlong φ hφi (pointFLTPlaceEquiv E F P) =
      pointFLTPlaceEquiv E F (Point.map (frobeniusAlgHom k K) P) := by
  apply (placeEquiv K F).symm.injective
  simp only [pointFLTPlaceEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  set w := (placeEquiv K F).symm
    (AlgebraicCurve.Place.restrictAlong φ hφi (placeEquiv K F (pointPlaceEquiv (E.baseChange K).toAffine F P)))
  have hmem : ∀ z, z ∈ w.toValuationSubring ↔
      φ z ∈ (pointPlaceEquiv (E.baseChange K).toAffine F P).toValuationSubring := fun _ => Iff.rfl
  let : Algebra k F := ((algebraMap K F).comp (algebraMap k K)).toAlgebra
  have hsub : ∀ u c : F, (u - c) ^ Fintype.card k = u ^ Fintype.card k - c ^ Fintype.card k :=
    fun u c => map_sub (frobeniusAlgHom k F) u c
  have hq : Fintype.card k ≠ 0 := Fintype.card_ne_zero
  rcases P with _ | ⟨a, b, h⟩
  · refine eq_placeOfPoint_zero (E.baseChange K).toAffine F w ?_
    rw [hmem, hφx]
    exact pow_notMem_valuationSubring _ (xF_notMem_placeOfPoint_zero (E.baseChange K).toAffine F) hq
  · rw [Point.map_some]
    refine eq_placeOfPoint_some (E.baseChange K).toAffine F w _ ?_ ?_
    · rw [hmem, map_inv₀, map_sub, hφx, AlgHom.commutes, frobeniusAlgHom_apply, map_pow,
        ← hsub, ← inv_pow]
      exact pow_notMem_valuationSubring _ (inv_sub_notMem_placeOfPoint (E.baseChange K).toAffine F h).1 hq
    · rw [hmem, map_inv₀, map_sub, hφy, AlgHom.commutes, frobeniusAlgHom_apply, map_pow,
        ← hsub, ← inv_pow]
      exact pow_notMem_valuationSubring _ (inv_sub_notMem_placeOfPoint (E.baseChange K).toAffine F h).2 hq
include hφx hφy in
theorem natCard_fixedPoints_restrictAlong_iterate (m : ℕ) :
    Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[m]) =
      Nat.card (Function.fixedPoints (Point.map (W' := E) (frobeniusAlgHom k K))^[m]) := by
  set e := pointFLTPlaceEquiv (K := K) E F
  have hsc : Function.Semiconj e (Point.map (W' := E) (frobeniusAlgHom k K))
      (AlgebraicCurve.Place.restrictAlong φ hφi) := fun P =>
    (restrictAlong_pointPlace E F φ hφi hφx hφy P).symm
  have hsc' := hsc.iterate_right m
  symm
  refine Nat.card_congr (e.subtypeEquiv fun P => ?_)
  simp only [Function.mem_fixedPoints, Function.IsFixedPt]
  rw [← hsc' P, e.apply_eq_iff_eq]
theorem frobeniusAlgHom_pow_apply (m : ℕ) (a : K) :
    (frobeniusAlgHom k K ^ m) a = a ^ Fintype.card k ^ m := by
  rw [AlgHom.coe_pow]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, frobeniusAlgHom_apply, ← pow_mul, ← pow_succ]
theorem point_map_iterate (σ : K →ₐ[k] K) (m : ℕ) :
    (Point.map (W' := E) σ)^[m] = Point.map (W' := E) (σ ^ m) := by
  induction m with
  | zero =>
    funext P
    rw [Function.iterate_zero, id, pow_zero]
    exact (Point.map_id P).symm
  | succ m ih =>
    funext P
    rw [Function.iterate_succ_apply, ih, Point.map_map, pow_succ]
    rfl
theorem range_algHom_eq {L : Type*} [Field L] [Fintype L] [Algebra k L] (ι : L →ₐ[k] K) {m : ℕ}
    (hm : m ≠ 0) (hL : Fintype.card L = Fintype.card k ^ m) :
    Set.range ι = {a : K | a ^ Fintype.card k ^ m = a} := by
  classical
  set N := Fintype.card k ^ m with hN
  have hsub : Set.range ι ⊆ {a : K | a ^ N = a} := by
    rintro _ ⟨c, rfl⟩
    change ι c ^ N = ι c
    rw [← map_pow, ← hL, FiniteField.pow_card]
  have hN1 : 1 < N := Nat.one_lt_pow hm (Fintype.one_lt_card)
  set Pp : K[X] := X ^ N - X
  have hP0 : Pp ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hN1
  have hroots : {a : K | a ^ N = a} = (Pp.roots.toFinset : Set K) := by
    ext a
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP0, IsRoot,
      Pp, eval_sub, eval_pow, eval_X, sub_eq_zero]
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (hroots ▸ Finset.finite_toSet _)
  rw [Set.ncard_range_of_injective (show Function.Injective ι from ι.toRingHom.injective),
    Nat.card_eq_fintype_card, hL, hroots,
    Set.ncard_coe_finset]
  calc Pp.roots.toFinset.card ≤ Multiset.card Pp.roots := Multiset.toFinset_card_le _
    _ ≤ Pp.natDegree := card_roots' _
    _ = N := FiniteField.X_pow_card_sub_X_natDegree_eq K hN1
theorem fixedPoints_eq_range {L : Type*} [Field L] [Fintype L] [DecidableEq L] [Algebra k L] (ι : L →ₐ[k] K)
    {m : ℕ} (hm : m ≠ 0) (hL : Fintype.card L = Fintype.card k ^ m) :
    Function.fixedPoints (Point.map (W' := E) (frobeniusAlgHom k K ^ m)) =
      Set.range (Point.map (W' := E) ι) := by
  have hrange := range_algHom_eq ι hm hL
  have hfix : ∀ a : K, (frobeniusAlgHom k K ^ m) a = a ↔ a ∈ Set.range ι := by
    intro a
    rw [frobeniusAlgHom_pow_apply, hrange]
    rfl
  ext P
  simp only [Function.mem_fixedPoints, Function.IsFixedPt, Set.mem_range]
  constructor
  · rcases P with _ | ⟨a, b, h⟩
    · exact fun _ => ⟨0, rfl⟩
    · intro hP
      rw [Point.map_some, Point.some.injEq] at hP
      obtain ⟨a', rfl⟩ := (hfix a).mp hP.1
      obtain ⟨b', rfl⟩ := (hfix b).mp hP.2
      exact ⟨.some a' b' ((E.toAffine.baseChange_nonsingular (show Function.Injective ι from ι.toRingHom.injective) a' b').mp h), rfl⟩
  · rintro ⟨P', rfl⟩
    rw [Point.map_map, show (frobeniusAlgHom k K ^ m).comp ι = ι from
      AlgHom.ext fun c => (hfix (ι c)).mpr ⟨c, rfl⟩]
include hφx hφy in
theorem natCard_point_eq_fixedPoints {L : Type*} [Field L] [Fintype L] [Algebra k L]
    {m : ℕ} (hm : m ≠ 0) (hL : Fintype.card L = Fintype.card k ^ m) :
    Nat.card (E.baseChange L).toAffine.Point =
      Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[m]) := by
  classical
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  let ι : L →ₐ[k] K := IsAlgClosed.lift
  rw [natCard_fixedPoints_restrictAlong_iterate E F φ hφi hφx hφy, point_map_iterate,
    fixedPoints_eq_range E ι hm hL, Nat.card_coe_set_eq,
    Set.ncard_range_of_injective (Point.map_injective ι)]
end Frobenius
end WeilConjectures.Bridge
end
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open Polynomial FiniteField
open scoped RatFunc Polynomial.Bivariate
noncomputable section
namespace WeilConjectures.Bridge
open FunctionField WeierstrassCurve.Affine
section Setup
variable {k₁ : Type*} [Field k₁] (W : WeierstrassCurve.Affine k₁)
  (K₁ : Type*) [Field K₁] [Algebra W.CoordinateRing K₁] [IsFractionRing W.CoordinateRing K₁]
theorem isScalarTower_constants_coordinateRing :
    letI := W.algebraPolynomial K₁
    letI := FunctionField.algebraConstants k₁ K₁
    IsScalarTower k₁ W.CoordinateRing K₁ :=
  letI := W.algebraPolynomial K₁
  letI := FunctionField.algebraConstants k₁ K₁
  IsScalarTower.of_algebraMap_eq fun _ => rfl
end Setup
section Main
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
  (E : WeierstrassCurve k) [E.IsElliptic]
  (K : Type*) [Field K] [IsAlgClosed K] [Algebra k K]
  (F₀ : Type*) [Field F₀] [Algebra E.toAffine.CoordinateRing F₀]
    [IsFractionRing E.toAffine.CoordinateRing F₀]
  (F : Type*) [Field F] [Algebra (E.baseChange K).toAffine.CoordinateRing F]
    [IsFractionRing (E.baseChange K).toAffine.CoordinateRing F]
theorem polynomial_baseChange :
    (E.baseChange K).toAffine.polynomial =
      E.toAffine.polynomial.map (mapRingHom (algebraMap k K)) :=
  WeierstrassCurve.Affine.map_polynomial (W := E.toAffine) (algebraMap k K)
include K F₀ F in
theorem hasse_of_functionFields :
    ∃ α β : ℂ, β = (starRingEnd ℂ) α ∧ ‖α‖ = Real.sqrt (Nat.card k) ∧
      ‖β‖ = Real.sqrt (Nat.card k) ∧
      ∀ (m : ℕ) [NeZero m],
        (Nat.card (E.baseChange (FiniteField.Extension k p m)).toAffine.Point : ℂ) =
          1 - α ^ m - β ^ m + (Nat.card k : ℂ) ^ m := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : Algebra k[X] F₀ := E.toAffine.algebraPolynomial F₀
  haveI : IsScalarTower k[X] E.toAffine.CoordinateRing F₀ := E.toAffine.algebraPolynomial_isScalarTower F₀
  letI : Algebra k⟮X⟯ F₀ := E.toAffine.algebraRatFunc F₀
  haveI : IsScalarTower k[X] k⟮X⟯ F₀ := E.toAffine.algebraRatFunc_isScalarTower F₀
  haveI : _root_.FunctionField k F₀ := E.toAffine.functionField F₀
  haveI : Algebra.IsSeparable k⟮X⟯ F₀ := E.toAffine.isSeparable F₀
  letI : Algebra k F₀ := FunctionField.algebraConstants k F₀
  haveI : IsScalarTower k k[X] F₀ := FunctionField.algebraConstants_isScalarTower k F₀
  haveI : IsScalarTower k E.toAffine.CoordinateRing F₀ := isScalarTower_constants_coordinateRing E.toAffine F₀
  haveI : AlgebraicCurve.IsCurveOver k F₀ := isCurveOver k F₀
  haveI : Algebra.EssFiniteType k F₀ := essFiniteType k F₀
  letI : Algebra K[X] F := (E.baseChange K).toAffine.algebraPolynomial F
  haveI : IsScalarTower K[X] (E.baseChange K).toAffine.CoordinateRing F := (E.baseChange K).toAffine.algebraPolynomial_isScalarTower F
  letI : Algebra K⟮X⟯ F := (E.baseChange K).toAffine.algebraRatFunc F
  haveI : IsScalarTower K[X] K⟮X⟯ F := (E.baseChange K).toAffine.algebraRatFunc_isScalarTower F
  haveI : _root_.FunctionField K F := (E.baseChange K).toAffine.functionField F
  haveI : Algebra.IsSeparable K⟮X⟯ F := (E.baseChange K).toAffine.isSeparable F
  letI : Algebra K F := FunctionField.algebraConstants K F
  haveI : IsScalarTower K K[X] F := FunctionField.algebraConstants_isScalarTower K F
  haveI : IsScalarTower K (E.baseChange K).toAffine.CoordinateRing F := isScalarTower_constants_coordinateRing (E.baseChange K).toAffine F
  haveI : IsFullConstantField K F := FunctionField.isFullConstantField_of_isAlgClosed K F
  haveI : AlgebraicCurve.IsCurveOver K F := isCurveOver K F
  have hgK : AlgebraicCurve.genusFF K F = 1 := genusFF_eq_one_of_isElliptic (E.baseChange K).toAffine F
  have hQ : (E.baseChange K).toAffine.polynomial = E.toAffine.polynomial.map (mapRingHom (algebraMap k K)) := polynomial_baseChange k E K
  have hmon : (E.baseChange K).toAffine.polynomial.Monic := (E.baseChange K).toAffine.monic_polynomial
  have hdeg : 0 < (E.baseChange K).toAffine.polynomial.natDegree := by rw [(E.baseChange K).toAffine.natDegree_polynomial]; norm_num
  have hinj : Function.Injective
      ((algebraMap (E.baseChange K).toAffine.CoordinateRing F).comp (adjoinRootBaseChange E.toAffine.polynomial (E.baseChange K).toAffine.polynomial hQ)) :=
    fun a b h => adjoinRootBaseChange_injective E.toAffine.polynomial
      (E.baseChange K).toAffine.polynomial hQ E.toAffine.monic_polynomial
      (IsFractionRing.injective (E.baseChange K).toAffine.CoordinateRing F h)
  letI : Algebra F₀ F := (IsFractionRing.lift hinj).toAlgebra
  have hcompat : ∀ r, algebraMap F₀ F (algebraMap E.toAffine.CoordinateRing F₀ r) =
      algebraMap (E.baseChange K).toAffine.CoordinateRing F (adjoinRootBaseChange E.toAffine.polynomial (E.baseChange K).toAffine.polynomial hQ r) :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  obtain ⟨φ, hφdef⟩ : ∃ φ, φ = frobFractionField E.toAffine.polynomial (E.baseChange K).toAffine.polynomial hQ F hmon hdeg :=
    ⟨_, rfl⟩
  have hφi : φ.toRingHom.IsIntegral := hφdef ▸ frobFractionField_isIntegral E.toAffine.polynomial (E.baseChange K).toAffine.polynomial hQ hmon hdeg
  have hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k) :=
    hφdef ▸ frobFractionField_apply_algebraMap E.toAffine.polynomial (E.baseChange K).toAffine.polynomial hQ F₀ hmon hdeg hcompat
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ :=
    adjoin_range_algebraMap_eq_top E.toAffine.polynomial (E.baseChange K).toAffine.polynomial hQ F₀ hcompat
  have hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤ :=
    exists_finset_adjoin_eq_top E.toAffine.polynomial F₀
  have hφx : φ (xF (E.baseChange K).toAffine F) = xF (E.baseChange K).toAffine F ^ Fintype.card k := by
    rw [hφdef, xF, frobFractionField_algebraMap, ← map_pow]
    congr 1
    change frobAdjoinRoot E.toAffine.polynomial (E.baseChange K).toAffine.polynomial hQ (AdjoinRoot.mk (E.baseChange K).toAffine.polynomial (C X)) = AdjoinRoot.mk (E.baseChange K).toAffine.polynomial (C X) ^ _
    rw [AdjoinRoot.mk_C, frobAdjoinRoot_of, expand_X, map_pow]
  have hφy : φ (yF (E.baseChange K).toAffine F) = yF (E.baseChange K).toAffine F ^ Fintype.card k := by
    rw [hφdef, yF, yCoord, frobFractionField_algebraMap, ← map_pow]
    congr 1
    change frobAdjoinRoot E.toAffine.polynomial (E.baseChange K).toAffine.polynomial hQ (AdjoinRoot.mk (E.baseChange K).toAffine.polynomial X) = AdjoinRoot.mk (E.baseChange K).toAffine.polynomial X ^ _
    rw [AdjoinRoot.mk_X, frobAdjoinRoot_root]
  obtain ⟨-, L, hLdeg, hL0, hLsymm, -, hRH, hcount⟩ :=
    lPolynomial_of_functionField k K F₀ F hfg hgen φ hφi hφ (N := placeCount k F₀)
      (fun _ _ => rfl)
  rw [hgK] at hLdeg hLsymm
  obtain ⟨Lc, hLc⟩ : ∃ Lc, Lc = L.map (Int.castRingHom ℂ) := ⟨_, rfl⟩
  rw [← hLc] at hRH hcount
  have hLc0 : Lc.coeff 0 = 1 := by rw [hLc]; simp [coeff_map, hL0]
  have hLc2 : Lc.coeff 2 = Nat.card k := by
    have h := hLsymm 0 (by norm_num)
    simp only [Nat.sub_zero, pow_zero, mul_one, pow_one, hL0] at h
    rw [hLc]; simp [coeff_map, h]
  have hLcdeg : Lc.natDegree = 2 := by
    rw [hLc, natDegree_map_eq_of_injective Int.cast_injective, hLdeg]
  have hcard : Multiset.card Lc.reverse.roots = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, reverse_natDegree,
      natTrailingDegree_eq_zero.mpr (.inr (by rw [hLc0]; exact one_ne_zero)), hLcdeg]
  obtain ⟨α, β, hαβ⟩ := Multiset.card_eq_two.mp hcard
  have hfac := eq_prod_one_sub_C_mul_X hLc0
  rw [hαβ] at hfac
  have hprod : α * β = Nat.card k := by
    have h2 := congrArg (fun f : ℂ[X] => f.coeff 2) hfac
    rw [hLc2] at h2
    rw [h2]
    have : ((({α, β} : Multiset ℂ).map fun a ↦ 1 - C a * X).prod : ℂ[X]) =
        C (α * β) * X ^ 2 - C (α + β) * X + 1 := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton, map_mul, map_add]
      ring
    rw [this, coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_one]
    norm_num
  have hnα : ‖α‖ = Real.sqrt (Nat.card k) := hRH α (by rw [hαβ]; simp)
  have hnβ : ‖β‖ = Real.sqrt (Nat.card k) := hRH β (by rw [hαβ]; simp)
  have hq0 : (0 : ℝ) < Nat.card k := by exact_mod_cast Nat.card_pos
  refine ⟨α, β, ?_, hnα, hnβ, fun m _ => ?_⟩
  ·
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnα
      exact (Real.sqrt_pos.mpr hq0).ne hnα
    have hconj : α * (starRingEnd ℂ) α = Nat.card k := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnα, Real.sq_sqrt hq0.le]
      push_cast
      rfl
    exact mul_left_cancel₀ hα0 (hprod.trans hconj.symm)
  ·
    have hm : m ≠ 0 := NeZero.ne m
    let : Fintype (FiniteField.Extension k p m) := Fintype.ofFinite _
    have hL : Fintype.card (FiniteField.Extension k p m) = Fintype.card k ^ m := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, natCard_extension]
    rw [natCard_point_eq_fixedPoints E F φ hφi hφx hφy hm hL,
      (AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
        k K F₀ F hfg hgen φ hφi hφ m (Nat.pos_of_ne_zero hm)).2]
    have h := hcount m (Nat.pos_of_ne_zero hm)
    rw [hαβ] at h
    simp only [placeCount] at h
    rw [h]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    ring
end Main
theorem hasse_elliptic_curve_proof (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k]
    [CharP k p] (E : WeierstrassCurve k) [E.IsElliptic] :
    ∃ α β : ℂ, β = (starRingEnd ℂ) α ∧ ‖α‖ = Real.sqrt (Nat.card k) ∧
      ‖β‖ = Real.sqrt (Nat.card k) ∧
      ∀ (m : ℕ) [NeZero m],
        (Nat.card (E.baseChange (FiniteField.Extension k p m)).toAffine.Point : ℂ) =
          1 - α ^ m - β ^ m + (Nat.card k : ℂ) ^ m :=
  hasse_of_functionFields p k E (AlgebraicClosure k) (FractionRing E.toAffine.CoordinateRing)
    (FractionRing (E.baseChange (AlgebraicClosure k)).toAffine.CoordinateRing)
end WeilConjectures.Bridge
end
end
open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures
theorem solution (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    (E : WeierstrassCurve k) [E.IsElliptic] :
    ∃ α β : ℂ, β = (starRingEnd ℂ) α ∧ ‖α‖ = Real.sqrt (Nat.card k) ∧ ‖β‖ = Real.sqrt (Nat.card k) ∧
      ∀ (m : ℕ) [NeZero m],
        (Nat.card (E.baseChange (FiniteField.Extension k p m)).toAffine.Point : ℂ) =
          1 - α ^ m - β ^ m + (Nat.card k : ℂ) ^ m :=
  WeilConjectures.Bridge.hasse_elliptic_curve_proof p k E
