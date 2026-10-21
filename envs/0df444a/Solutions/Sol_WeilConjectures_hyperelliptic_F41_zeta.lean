-- Prove2me | solution 1 for WeilConjectures.hyperelliptic_F41_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T15:33:49.851781+00:00
-- url     : https://prove2.me/submissions/53f8cb99-31b9-418c-b9ff-47039073a15d

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
import Theorems.Thm_WeilConjectures_hyperelliptic_F41_point_counts
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_FunctionField_Chart_placeValuation_algebraMap_eq_one
import Theorems.Thm_FunctionField_genus_eq_genusChart
import Theorems.Thm_WeilConjectures_Bridge_genusFF_eq_genus
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
open scoped nonZeroDivisors Polynomial RatFunc WithZero
open Polynomial BigOperators Submodule IntermediateField
noncomputable section
namespace FunctionField.Chart
section TranscendentalPowers
variable (k L : Type*) [Field k] [Field L] [Algebra k L]
end TranscendentalPowers
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
variable [IsFullConstantField k K]
attribute [local instance] FunctionField.Chart.instDecidableEqPlaceAPolar
attribute [local instance] FunctionField.Chart.instDecidableEqRatFuncPolar
section PolarDivisor
section ChartVariable
attribute [local instance] FunctionField.Chart.instIsScalarTowerChart
end ChartVariable
section Auxiliary
omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem algebraMap_polynomial_eq_aeval_XK (p : k[X]) :
    algebraMap k[X] K p = aeval (XK k K) p := by
  have h : IsScalarTower.toAlgHom k k[X] K = aeval (XK k K) := by
    refine Polynomial.algHom_ext ?_
    rw [IsScalarTower.toAlgHom_apply, aeval_X,
      IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, RatFunc.algebraMap_X]
    rfl
  calc algebraMap k[X] K p = IsScalarTower.toAlgHom k k[X] K p := rfl
    _ = aeval (XK k K) p := by rw [h]
end Auxiliary
end PolarDivisor
end FunctionField.Chart
end
end
end
section
section
open Polynomial
open scoped Polynomial.Bivariate RatFunc nonZeroDivisors
noncomputable section
namespace WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k)
namespace CoordinateRing
end CoordinateRing
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
section AbstractPolynomialAlgebra
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
section AbstractRatFuncAlgebra
variable [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
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
open Polynomial
noncomputable section
namespace WeilConjectures.Bridge.Hyperelliptic
theorem coeff_one_zetaOfCounts (N : ℕ → ℕ) :
    PowerSeries.coeff 1 (zetaOfCounts N) = N 1 := by
  have h := congrArg (PowerSeries.coeff 0) (derivative_zetaOfCounts N)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton] at h
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_zetaOfCounts] at h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_countingSeries] at h
  simpa using h
theorem coeff_two_zetaOfCounts (N : ℕ → ℕ) :
    PowerSeries.coeff 2 (zetaOfCounts N) = ((N 1 : ℚ) ^ 2 + N 2) / 2 := by
  have h := congrArg (PowerSeries.coeff 1) (derivative_zetaOfCounts N)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
    Finset.sum_cons, Finset.Nat.antidiagonal_zero, Finset.map_singleton,
    Finset.sum_singleton] at h
  simp at h
  rw [coeff_one_zetaOfCounts, constantCoeff_zetaOfCounts] at h
  linarith
theorem mul_oneSub_eq (Z : PowerSeries ℚ) (q : ℚ) :
    Z * ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) =
      Z - PowerSeries.C (1 + q) * (Z * PowerSeries.X) +
        PowerSeries.C q * (Z * PowerSeries.X ^ 2) := by
  rw [map_add, map_one]
  ring
theorem coeff_one_mul_oneSub (Z : PowerSeries ℚ) (q : ℚ) :
    PowerSeries.coeff 1 (Z * ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))) =
      PowerSeries.coeff 1 Z - (1 + q) * PowerSeries.coeff 0 Z := by
  rw [mul_oneSub_eq, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_X_pow', if_neg (by norm_num)]
  ring
theorem coeff_two_mul_oneSub (Z : PowerSeries ℚ) (q : ℚ) :
    PowerSeries.coeff 2 (Z * ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))) =
      PowerSeries.coeff 2 Z - (1 + q) * PowerSeries.coeff 1 Z + q * PowerSeries.coeff 0 Z := by
  rw [mul_oneSub_eq, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_X_pow', if_pos (by norm_num)]
def countF41 [Fact (Nat.Prime 41)] (m : ℕ) : ℕ :=
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    Nat.card {xy : FiniteField.Extension (ZMod 41) 41 m × FiniteField.Extension (ZMod 41) 41 m //
      xy.2 ^ 2 + xy.2 = xy.1 ^ 5} + 1
theorem natCard_sol_congr {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Nat.card {xy : A × A // xy.2 ^ 2 + xy.2 = xy.1 ^ 5} =
      Nat.card {xy : B × B // xy.2 ^ 2 + xy.2 = xy.1 ^ 5} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) fun xy => ?_)
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, RingEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe]
  rw [← map_pow, ← map_add, ← map_pow, e.injective.eq_iff]
theorem ringEquiv_of_natCard_eq {A B : Type*} [Field A] [Field B] [Finite A] [Finite B]
    (h : Nat.card A = Nat.card B) : Nonempty (A ≃+* B) := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  exact ⟨FiniteField.ringEquivOfCardEq (K := A) (K' := B)
    (by rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card])⟩
theorem countF41_one [Fact (Nat.Prime 41)] : countF41 1 = 33 := by
  rw [countF41, dif_neg one_ne_zero]
  obtain ⟨e⟩ := ringEquiv_of_natCard_eq (A := FiniteField.Extension (ZMod 41) 41 1)
    (B := ZMod 41) (by rw [FiniteField.natCard_extension, Nat.card_zmod, pow_one])
  rw [natCard_sol_congr e]
  exact WeilConjectures.hyperelliptic_F41_point_counts.1
theorem countF41_two [Fact (Nat.Prime 41)] : countF41 2 = 1743 := by
  rw [countF41, dif_neg two_ne_zero]
  obtain ⟨e⟩ := ringEquiv_of_natCard_eq (A := FiniteField.Extension (ZMod 41) 41 2)
    (B := GaloisField 41 2)
    (by rw [FiniteField.natCard_extension, Nat.card_zmod, GaloisField.card 41 2 two_ne_zero])
  rw [natCard_sol_congr e]
  exact WeilConjectures.hyperelliptic_F41_point_counts.2
@[simp] theorem coe_ofNat_powerSeries (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : ℚ[X])) : PowerSeries ℚ) = OfNat.ofNat n := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat]
theorem zeta_eq_of_lPolynomial [Fact (Nat.Prime 41)] (L : ℤ[X]) (hLdeg : L.natDegree = 2 * 2)
    (hL0 : L.coeff 0 = 1)
    (hLsymm : ∀ i ≤ 2 * 2, L.coeff (2 * 2 - i) * (41 : ℤ) ^ i = (41 : ℤ) ^ 2 * L.coeff i)
    (hrat : zetaOfCounts countF41 *
        (((1 - X : ℤ[X]).map (Int.castRingHom ℚ) : PowerSeries ℚ) *
          ((1 - C (41 : ℤ) * X : ℤ[X]).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        (L.map (Int.castRingHom ℚ) : PowerSeries ℚ)) :
    zetaOfCounts countF41 * ((1 - PowerSeries.X) * (1 - 41 * PowerSeries.X)) =
      1 - 9 * PowerSeries.X + 71 * PowerSeries.X ^ 2 - 9 * 41 * PowerSeries.X ^ 3 +
        41 ^ 2 * PowerSeries.X ^ 4 := by
  have hrat' : zetaOfCounts countF41 *
      ((1 - PowerSeries.X) * (1 - PowerSeries.C (41 : ℚ) * PowerSeries.X)) =
      (L.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
    rw [← hrat, show PowerSeries.C (41 : ℚ) = 41 from map_ofNat PowerSeries.C 41]
    simp
  have hcoeff : ∀ n, (L.coeff n : ℚ) =
      PowerSeries.coeff n (zetaOfCounts countF41 *
        ((1 - PowerSeries.X) * (1 - PowerSeries.C (41 : ℚ) * PowerSeries.X))) := by
    intro n
    rw [hrat', Polynomial.coeff_coe, coeff_map, eq_intCast]
  have hz0 : PowerSeries.coeff 0 (zetaOfCounts countF41) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_zetaOfCounts]
  have hL1 : L.coeff 1 = -9 := by
    have h := hcoeff 1
    rw [coeff_one_mul_oneSub, coeff_one_zetaOfCounts, countF41_one, hz0] at h
    have : (L.coeff 1 : ℚ) = -9 := by rw [h]; norm_num
    exact_mod_cast this
  have hL2 : L.coeff 2 = 71 := by
    have h := hcoeff 2
    rw [coeff_two_mul_oneSub, coeff_two_zetaOfCounts, coeff_one_zetaOfCounts, countF41_one,
      countF41_two, hz0] at h
    have : (L.coeff 2 : ℚ) = 71 := by rw [h]; norm_num
    exact_mod_cast this
  have hL3 : L.coeff 3 = -9 * 41 := by
    have h := hLsymm 1 (by norm_num)
    rw [hL1] at h
    norm_num at h
    linarith
  have hL4 : L.coeff 4 = 41 ^ 2 := by
    have h := hLsymm 0 (by norm_num)
    rw [hL0] at h
    norm_num at h
    linarith
  have hLeq : L = C 1 - C 9 * X + C 71 * X ^ 2 - C 369 * X ^ 3 + C 1681 * X ^ 4 := by
    ext n
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [hL0, hL1, hL2, hL3, hL4, coeff_X, coeff_one, coeff_X_pow]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      split_ifs <;> omega
  rw [hLeq] at hrat
  simp at hrat
  convert hrat using 1
  norm_num
end WeilConjectures.Bridge.Hyperelliptic
end
end
section
open Polynomial
open scoped Polynomial.Bivariate
namespace WeilConjectures.Bridge.Hyperelliptic
noncomputable section
variable (k : Type*) [Field k]
def hypPoly : k[X][Y] := Y ^ 2 + Y - C (X ^ 5)
abbrev HypRing : Type _ := AdjoinRoot (hypPoly k)
lemma hypPoly_eq : hypPoly k = Y ^ 2 + (Y - C (X ^ 5)) := by
  rw [hypPoly, add_sub_assoc]
lemma hypPoly_monic : (hypPoly k).Monic := by
  rw [hypPoly_eq]
  refine monic_X_pow_add ?_
  refine (degree_sub_le _ _).trans_lt ?_
  rw [degree_X, degree_C (pow_ne_zero 5 X_ne_zero)]
  norm_num
lemma hypPoly_natDegree : (hypPoly k).natDegree = 2 := by
  rw [hypPoly_eq, natDegree_add_eq_left_of_degree_lt]
  · exact natDegree_X_pow 2
  · refine (degree_sub_le _ _).trans_lt ?_
    rw [degree_X, degree_C (pow_ne_zero 5 X_ne_zero), degree_X_pow]
    norm_num
lemma natDegree_sq_add_self (b : k[X]) : (b ^ 2 + b).natDegree = 2 * b.natDegree := by
  rcases eq_or_ne b.natDegree 0 with hb | hb
  · obtain ⟨c, rfl⟩ : ∃ c, b = C c := ⟨_, eq_C_of_natDegree_eq_zero hb⟩
    rw [← C_pow, ← C_add, natDegree_C, natDegree_C]
  · have hlt : b.natDegree < (b ^ 2).natDegree := by
      rw [natDegree_pow]
      omega
    rw [natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_pow]
lemma hypPoly_not_isRoot (b : k[X]) : ¬ (hypPoly k).IsRoot b := by
  intro h
  have h' : b ^ 2 + b = X ^ 5 := by
    simpa [hypPoly, IsRoot, sub_eq_zero] using h
  have := congrArg natDegree h'
  rw [natDegree_sq_add_self, natDegree_X_pow] at this
  omega
lemma hypPoly_irreducible : Irreducible (hypPoly k) := by
  rw [(hypPoly_monic k).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [hypPoly_natDegree]) (by rw [hypPoly_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun b hb => ?_
  exact hypPoly_not_isRoot k b ((mem_roots (hypPoly_monic k).ne_zero).mp hb)
instance : IsDomain (HypRing k) :=
  AdjoinRoot.isDomain_of_prime (hypPoly_irreducible k).prime
def xR : HypRing k := algebraMap k[X] (HypRing k) X
def yR : HypRing k := AdjoinRoot.root (hypPoly k)
lemma yR_sq_add_yR : yR k ^ 2 + yR k = xR k ^ 5 := by
  have h : AdjoinRoot.mk (hypPoly k) (Y ^ 2 + Y - C (X ^ 5)) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_add, AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X, map_pow,
    sub_eq_zero] at h
  exact h
def basis : Module.Basis (Fin 2) k[X] (HypRing k) :=
  ((AdjoinRoot.powerBasis' (hypPoly_monic k)).basis).reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, hypPoly_natDegree]))
@[simp] lemma basis_zero : basis k 0 = 1 := by
  simp [basis, AdjoinRoot.powerBasis'_gen]
@[simp] lemma basis_one : basis k 1 = yR k := by
  simp [basis, AdjoinRoot.powerBasis'_gen, yR]
instance : Module.Finite k[X] (HypRing k) := Module.Finite.of_basis (basis k)
lemma algebraMap_injective : Function.Injective (algebraMap k[X] (HypRing k)) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero (by
    rw [degree_eq_natDegree (hypPoly_monic k).ne_zero, hypPoly_natDegree]; decide)
instance : FaithfulSMul k[X] (HypRing k) :=
  (faithfulSMul_iff_algebraMap_injective k[X] (HypRing k)).mpr (algebraMap_injective k)
instance : Algebra.IsIntegral k[X] (HypRing k) := Algebra.IsIntegral.of_finite k[X] _
lemma exists_eq_add_mul_yR (r : HypRing k) :
    ∃ p q : k[X], algebraMap k[X] (HypRing k) p + algebraMap k[X] (HypRing k) q * yR k = r := by
  refine ⟨(basis k).repr r 0, (basis k).repr r 1, ?_⟩
  conv_rhs => rw [← (basis k).sum_repr r]
  rw [Fin.sum_univ_two, basis_zero, basis_one, Algebra.smul_def, Algebra.smul_def, mul_one]
lemma hypPoly_map {K : Type*} [Field K] (f : k →+* K) :
    (hypPoly k).map (mapRingHom f) = hypPoly K := by
  simp [hypPoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow]
def xPoly : k[X][Y] := Y ^ 5 - C (X ^ 2 + X)
lemma xPoly_eq_neg_swap : xPoly k = -Polynomial.Bivariate.swap (hypPoly k) := by
  simp only [xPoly, hypPoly, map_sub, map_add, map_pow, Polynomial.Bivariate.swap_Y,
    Polynomial.Bivariate.swap_C, Polynomial.map_X]
  ring
lemma xPoly_monic : (xPoly k).Monic := by
  rw [xPoly, sub_eq_add_neg]
  refine monic_X_pow_add ?_
  rw [degree_neg, degree_C]
  · norm_num
  · intro h
    have := congrArg natDegree h
    rw [natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow,
      natDegree_zero] at this
    omega
def xAdjoinRootEquiv : AdjoinRoot (xPoly k) ≃ₐ[k] HypRing k :=
  { Ideal.quotientEquiv
      (Ideal.span {xPoly k}) (Ideal.span {hypPoly k})
      Polynomial.Bivariate.swap.toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton, xPoly_eq_neg_swap,
        map_neg, Ideal.span_singleton_neg]
      exact congrArg (fun p => Ideal.span ({p} : Set k[X][Y]))
        (Polynomial.Bivariate.swap_swap_apply (hypPoly k)).symm) with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply k k[X] (AdjoinRoot (xPoly k)),
        IsScalarTower.algebraMap_apply k k[X] (HypRing k)]
      change (Ideal.quotientEquiv _ _ Polynomial.Bivariate.swap.toRingEquiv _)
        (Ideal.Quotient.mk _ (C (C r))) = Ideal.Quotient.mk _ (C (C r))
      rw [Ideal.quotientEquiv_mk]
      exact congrArg (Ideal.Quotient.mk (Ideal.span {hypPoly k}))
        (Polynomial.Bivariate.swap_C_C r) }
lemma xAdjoinRootEquiv_mk (q : k[X][Y]) :
    xAdjoinRootEquiv k (AdjoinRoot.mk (xPoly k) q) =
      AdjoinRoot.mk (hypPoly k) (Polynomial.Bivariate.swap q) := rfl
end
end WeilConjectures.Bridge.Hyperelliptic
end
section
open Polynomial
open scoped Polynomial.Bivariate
namespace WeilConjectures.Bridge.Hyperelliptic
noncomputable section
variable (k : Type*) [Field k]
lemma mk_derivative_hypPoly :
    AdjoinRoot.mk (hypPoly k) (derivative (hypPoly k)) = 2 * yR k + 1 := by
  change AdjoinRoot.mk (hypPoly k) (derivative (Y ^ 2 + Y - C (X ^ 5))) = _
  rw [derivative_sub, derivative_C, sub_zero, derivative_add, derivative_X_pow, derivative_X]
  simp only [map_add, map_mul, map_one, AdjoinRoot.mk_C, yR]
  norm_num
  left
  exact map_ofNat _ 2
lemma derivative_xPoly : derivative (xPoly k) = 5 * Y ^ 4 := by
  rw [xPoly, derivative_sub, derivative_C, sub_zero, derivative_X_pow]
  norm_num
  exact map_ofNat C 5
lemma xAdjoinRootEquiv_mk_derivative :
    xAdjoinRootEquiv k (AdjoinRoot.mk (xPoly k) (derivative (xPoly k))) = 5 * xR k ^ 4 := by
  rw [derivative_xPoly, xAdjoinRootEquiv_mk]
  simp only [map_mul, map_pow, map_ofNat, Polynomial.Bivariate.swap_Y, AdjoinRoot.mk_C]
  rfl
instance : IsDomain (AdjoinRoot (xPoly k)) :=
  (xAdjoinRootEquiv k).injective.isDomain (xAdjoinRootEquiv k).toRingHom
lemma derivatives_not_both_mem [NeZero (5 : k)] (𝔭 : Ideal (HypRing k)) [h𝔭 : 𝔭.IsPrime] :
    2 * yR k + 1 ∉ 𝔭 ∨ 5 * xR k ^ 4 ∉ 𝔭 := by
  by_contra! h
  obtain ⟨hy, hx⟩ := h
  have h5 : IsUnit (5 : HypRing k) := by
    have := (isUnit_iff_ne_zero.mpr (NeZero.ne (5 : k))).map (algebraMap k (HypRing k))
    rwa [map_ofNat] at this
  have hx1 : xR k ∈ 𝔭 := by
    rcases h𝔭.mem_or_mem hx with h | h
    · exact absurd (𝔭.eq_top_of_isUnit_mem h h5) h𝔭.ne_top
    · exact h𝔭.mem_of_pow_mem 4 h
  have hx5 : xR k ^ 5 ∈ 𝔭 := 𝔭.pow_mem_of_mem hx1 5 (by norm_num)
  have h1 : (1 : HypRing k) = (2 * yR k + 1) * (2 * yR k + 1) - 4 * xR k ^ 5 := by
    rw [← yR_sq_add_yR]
    ring
  have hmem : (1 : HypRing k) ∈ 𝔭 := by
    rw [h1]
    exact 𝔭.sub_mem (𝔭.mul_mem_left _ hy) (𝔭.mul_mem_left _ hx5)
  exact h𝔭.ne_top ((Ideal.eq_top_iff_one 𝔭).mpr hmem)
theorem isDiscreteValuationRing_atPrime_of_y [NeZero (5 : k)]
    (𝔭 : Ideal (HypRing k)) [𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) (hy : 2 * yR k + 1 ∉ 𝔭) :
    IsDiscreteValuationRing (Localization.AtPrime 𝔭) := by
  apply AdjoinRoot.isDiscreteValuationRing_atPrime_of_derivative_not_mem
    (hypPoly k) (hypPoly_monic k) 𝔭 h0
  rwa [mk_derivative_hypPoly]
theorem isDiscreteValuationRing_atPrime_of_x [NeZero (5 : k)]
    (𝔭 : Ideal (HypRing k)) [𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥)
    (hx : 5 * xR k ^ 4 ∉ 𝔭) :
    IsDiscreteValuationRing (Localization.AtPrime 𝔭) := by
  let e := (xAdjoinRootEquiv k).toRingEquiv
  let 𝔮 := 𝔭.comap e.toRingHom
  have h𝔮0 : 𝔮 ≠ ⊥ := by
    intro h
    apply h0
    rw [← Ideal.map_comap_eq_self_of_equiv e 𝔭]
    change 𝔮.map e.toRingHom = ⊥
    rw [h, Ideal.map_bot]
  have : IsDiscreteValuationRing (Localization.AtPrime 𝔮) :=
    AdjoinRoot.isDiscreteValuationRing_atPrime_of_derivative_not_mem
      (xPoly k) (xPoly_monic k) 𝔮 h𝔮0 (by
        intro hmem
        apply hx
        rw [← xAdjoinRootEquiv_mk_derivative]
        simpa [𝔮, e] using hmem)
  exact IsDiscreteValuationRing.atPrime_of_comap_ringEquiv e 𝔭 h0
theorem isDedekindDomainDvr [NeZero (5 : k)] : IsDedekindDomainDvr (HypRing k) := by
  have : IsNoetherianRing (HypRing k) := IsNoetherianRing.of_finite k[X] _
  refine { is_dvr_at_nonzero_prime := ?_ }
  intro 𝔭 h0 h𝔭
  rcases derivatives_not_both_mem k 𝔭 with hy | hx
  · exact isDiscreteValuationRing_atPrime_of_y k 𝔭 h0 hy
  · exact isDiscreteValuationRing_atPrime_of_x k 𝔭 h0 hx
instance [NeZero (5 : k)] : IsDedekindDomain (HypRing k) :=
  have := isDedekindDomainDvr k
  inferInstance
end
end WeilConjectures.Bridge.Hyperelliptic
end
section
open Polynomial
open scoped Polynomial.Bivariate RatFunc nonZeroDivisors
namespace WeilConjectures.Bridge.Hyperelliptic
noncomputable section
variable (k : Type*) [Field k]
lemma derivative_hypPoly_ne_zero : derivative (hypPoly k) ≠ 0 := by
  intro h
  have := congrArg (fun p => Polynomial.coeff p 0) h
  simp only [coeff_derivative, coeff_zero, hypPoly, coeff_sub, coeff_add, coeff_X_pow,
    coeff_X, coeff_C_succ] at this
  norm_num at this
variable (F : Type*) [Field F] [Algebra (HypRing k) F] [IsFractionRing (HypRing k) F]
@[reducible]
def algebraPolynomial : Algebra k[X] F :=
  ((algebraMap (HypRing k) F).comp (algebraMap k[X] (HypRing k))).toAlgebra
omit [IsFractionRing (HypRing k) F] in
theorem algebraPolynomial_isScalarTower :
    letI := algebraPolynomial k F
    IsScalarTower k[X] (HypRing k) F :=
  letI := algebraPolynomial k F
  IsScalarTower.of_algebraMap_eq fun _ => rfl
section AbstractPolynomialAlgebra
variable [Algebra k[X] F] [IsScalarTower k[X] (HypRing k) F]
theorem algebraMap_polynomial_injective : Function.Injective (algebraMap k[X] F) := by
  rw [IsScalarTower.algebraMap_eq k[X] (HypRing k) F]
  exact (IsFractionRing.injective (HypRing k) F).comp (algebraMap_injective k)
@[reducible]
def algebraRatFunc : Algebra k⟮X⟯ F :=
  (IsFractionRing.lift (algebraMap_polynomial_injective k F)).toAlgebra
theorem algebraRatFunc_isScalarTower :
    letI := algebraRatFunc k F
    IsScalarTower k[X] k⟮X⟯ F := by
  let := algebraRatFunc k F
  refine IsScalarTower.of_algebraMap_eq fun p => ?_
  exact (IsFractionRing.lift_algebraMap (algebraMap_polynomial_injective k F) p).symm
section AbstractRatFuncAlgebra
variable [Algebra k⟮X⟯ F] [IsScalarTower k[X] k⟮X⟯ F]
def yF : F := algebraMap (HypRing k) F (yR k)
def basisRatFunc : Module.Basis (Fin 2) k⟮X⟯ F :=
  (basis k).localizationLocalization k⟮X⟯ k[X]⁰ F
@[simp]
theorem basisRatFunc_zero : basisRatFunc k F 0 = 1 := by
  rw [basisRatFunc, Module.Basis.localizationLocalization_apply, basis_zero, map_one]
@[simp]
theorem basisRatFunc_one : basisRatFunc k F 1 = yF k F := by
  rw [basisRatFunc, Module.Basis.localizationLocalization_apply, basis_one, yF]
theorem functionField : _root_.FunctionField k F :=
  Module.Finite.of_basis (basisRatFunc k F)
theorem finrank_ratFunc_eq_two : Module.finrank k⟮X⟯ F = 2 := by
  rw [Module.finrank_eq_card_basis (basisRatFunc k F), Fintype.card_fin]
omit [IsFractionRing (HypRing k) F] in
theorem aeval_yF :
    Polynomial.aeval (yF k F) ((hypPoly k).map (algebraMap k[X] k⟮X⟯)) = 0 := by
  have h1 : eval₂ (algebraMap k[X] F) (yF k F) (hypPoly k) = 0 := by
    rw [IsScalarTower.algebraMap_eq k[X] (HypRing k) F, yF]
    change eval₂ ((algebraMap (HypRing k) F).comp (AdjoinRoot.of (hypPoly k)))
      ((algebraMap (HypRing k) F) (AdjoinRoot.root (hypPoly k))) (hypPoly k) = 0
    rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq k[X] k⟮X⟯ F]
  exact h1
omit [IsFractionRing (HypRing k) F] in
theorem yF_isIntegral : _root_.IsIntegral k⟮X⟯ (yF k F) :=
  ⟨(hypPoly k).map (algebraMap k[X] k⟮X⟯), (hypPoly_monic k).map _, by
    rw [← Polynomial.aeval_def]; exact aeval_yF k F⟩
theorem yF_notMem_range : yF k F ∉ Set.range (algebraMap k⟮X⟯ F) := by
  rintro ⟨c, hc⟩
  have h := Fintype.linearIndependent_iff.mp (basisRatFunc k F).linearIndependent ![c, -1]
  have h1 : (![c, -1] : Fin 2 → k⟮X⟯) 1 = 0 := by
    refine h ?_ 1
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, basisRatFunc_zero, basisRatFunc_one]
    rw [← hc, Algebra.smul_def, mul_one, neg_one_smul, add_neg_cancel]
  norm_num at h1
theorem minpoly_yF :
    minpoly k⟮X⟯ (yF k F) = (hypPoly k).map (algebraMap k[X] k⟮X⟯) := by
  have hmonic : ((hypPoly k).map (algebraMap k[X] k⟮X⟯)).Monic := (hypPoly_monic k).map _
  have hdvd : minpoly k⟮X⟯ (yF k F) ∣ (hypPoly k).map (algebraMap k[X] k⟮X⟯) :=
    minpoly.dvd k⟮X⟯ (yF k F) (aeval_yF k F)
  have hdeg : ((hypPoly k).map (algebraMap k[X] k⟮X⟯)).natDegree = 2 := by
    rw [(hypPoly_monic k).natDegree_map, hypPoly_natDegree]
  have hle : (minpoly k⟮X⟯ (yF k F)).natDegree ≤ 2 := by
    rw [← hdeg]; exact natDegree_le_of_dvd hdvd hmonic.ne_zero
  have hge : 2 ≤ (minpoly k⟮X⟯ (yF k F)).natDegree := by
    rcases Nat.lt_or_ge (minpoly k⟮X⟯ (yF k F)).natDegree 2 with hlt | hge
    · have hpos := minpoly.natDegree_pos (yF_isIntegral k F)
      have h1 : (minpoly k⟮X⟯ (yF k F)).natDegree = 1 := by omega
      exact absurd (minpoly.natDegree_eq_one_iff.mp h1) (yF_notMem_range k F)
    · exact hge
  have heq : (minpoly k⟮X⟯ (yF k F)).natDegree = 2 := le_antisymm hle hge
  obtain ⟨c, hc⟩ := hdvd
  have hmp : (minpoly k⟮X⟯ (yF k F)).Monic := minpoly.monic (yF_isIntegral k F)
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
set_option synthInstance.maxHeartbeats 200000 in
theorem isSeparable : Algebra.IsSeparable k⟮X⟯ F := by
  have hsep : IsSeparable k⟮X⟯ (yF k F) := by
    rw [IsSeparable, separable_iff_derivative_ne_zero
      (minpoly.irreducible (yF_isIntegral k F)), minpoly_yF, Polynomial.derivative_map]
    intro hzero
    rw [Polynomial.map_eq_zero_iff (IsFractionRing.injective k[X] k⟮X⟯)] at hzero
    exact derivative_hypPoly_ne_zero k hzero
  have htop : IntermediateField.adjoin k⟮X⟯ {yF k F} = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span k⟮X⟯ (Set.range (basisRatFunc k F)) := by
      rw [(basisRatFunc k F).span_eq]; trivial
    have hle : Submodule.span k⟮X⟯ (Set.range (basisRatFunc k F)) ≤
        Subalgebra.toSubmodule (IntermediateField.adjoin k⟮X⟯ {yF k F}).toSubalgebra := by
      rw [Submodule.span_le, Set.range_subset_iff]
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule, basisRatFunc_zero]
        exact one_mem _
      · simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule, basisRatFunc_one]
        exact IntermediateField.mem_adjoin_simple_self k⟮X⟯ (yF k F)
    exact hle hz
  have : Algebra.IsSeparable k⟮X⟯ (IntermediateField.adjoin k⟮X⟯ {yF k F}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k⟮X⟯ F).mpr hsep
  exact AlgEquiv.Algebra.isSeparable
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
end AbstractRatFuncAlgebra
end AbstractPolynomialAlgebra
end
end WeilConjectures.Bridge.Hyperelliptic
end
section
open FunctionField
open FunctionField.Chart
open Polynomial
open scoped Polynomial RatFunc
namespace WeilConjectures.Bridge.Hyperelliptic
noncomputable section
variable (k : Type*) [Field k]
variable (F : Type*) [Field F] [Algebra (HypRing k) F] [IsFractionRing (HypRing k) F]
variable [Algebra k[X] F] [IsScalarTower k[X] (HypRing k) F]
  [Algebra k⟮X⟯ F] [IsScalarTower k[X] k⟮X⟯ F]
  [_root_.FunctionField k F] [Algebra.IsSeparable k⟮X⟯ F]
local notation "A∞" => inftyValuationSubring k
local notation "S∞" => infiniteIntegers k F
local instance instFaithfulInfinity : FaithfulSMul A∞ S∞ :=
  FaithfulSMul.of_field_isFractionRing A∞ S∞ k⟮X⟯ F
local instance instNoZeroSMulDivisorsInfinity : NoZeroSMulDivisors A∞ S∞ := ⟨by
  intro c x h
  rw [Algebra.smul_def] at h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hc | hx
  · exact Or.inl ((faithfulSMul_iff_algebraMap_injective A∞ S∞).mp inferInstance
      (by simpa using hc))
  · exact Or.inr hx
⟩
omit [IsFractionRing (HypRing k) F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] in
lemma xF_eq_XK : algebraMap (HypRing k) F (xR k) = XK k F := by
  rw [xR, ← IsScalarTower.algebraMap_apply k[X] (HypRing k) F,
    IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F]
  exact congrArg (algebraMap k⟮X⟯ F) (RatFunc.algebraMap_X (K := k))
omit [IsFractionRing (HypRing k) F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] in
lemma yF_equation : yF k F ^ 2 + yF k F = XK k F ^ 5 := by
  have h := congrArg (algebraMap (HypRing k) F) (yR_sq_add_yR k)
  rwa [map_add, map_pow, map_pow, xF_eq_XK] at h
def infinityZ : F := yF k F * (tK k F) ^ 3
omit [IsFractionRing (HypRing k) F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] in
lemma infinityZ_equation :
    (infinityZ k F) ^ 2 + (tK k F) ^ 3 * infinityZ k F - tK k F = 0 := by
  have heq := yF_equation k F
  have hxt : XK k F * tK k F = 1 := XK_mul_tK k F
  dsimp [infinityZ]
  linear_combination (tK k F) ^ 6 * heq +
    tK k F * ((XK k F * tK k F) ^ 4 + (XK k F * tK k F) ^ 3 + (XK k F * tK k F) ^ 2 +
      XK k F * tK k F + 1) * hxt
omit [IsFractionRing (HypRing k) F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] in
lemma infinityZ_isIntegral : _root_.IsIntegral A∞ (infinityZ k F) := by
  let t : A∞ := tA k
  refine ⟨X ^ 2 + C (t ^ 3) * X + C (-t), (isMonicOfDegree_add_add_two _ _).monic, ?_⟩
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
  have htmap : algebraMap A∞ F (tA k) = tK k F := rfl
  simp only [map_neg, map_pow, t, htmap]
  linear_combination infinityZ_equation k F
def infinityZInt : S∞ :=
  ⟨infinityZ k F, (mem_integralClosure_iff (R := A∞) (A := F)).2 (infinityZ_isIntegral k F)⟩
def infinityTInt : S∞ := algebraMap A∞ S∞ (tA k)
omit [IsFractionRing (HypRing k) F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] in
lemma infinityZInt_equation :
    (infinityZInt k F) ^ 2 + (infinityTInt k F) ^ 3 * infinityZInt k F -
      infinityTInt k F = 0 := by
  apply Subtype.ext
  change (infinityZ k F) ^ 2 + (algebraMap A∞ F (tA k)) ^ 3 * infinityZ k F -
    algebraMap A∞ F (tA k) = 0
  exact infinityZ_equation k F
omit [IsFractionRing (HypRing k) F] in
lemma infinity_map_maximalIdeal_le_sq
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    Ideal.map (algebraMap A∞ S∞) (IsLocalRing.maximalIdeal A∞) ≤ v.asIdeal ^ 2 := by
  let P := v.asIdeal
  let z := infinityZInt k F
  let t := infinityTInt k F
  have hunder : P.under A∞ = IsLocalRing.maximalIdeal A∞ :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  have hmap : Ideal.map (algebraMap A∞ S∞) (IsLocalRing.maximalIdeal A∞) ≤ P := by
    rw [← hunder]
    exact Ideal.map_comap_le
  have htA : tA k ∈ IsLocalRing.maximalIdeal A∞ := by
    rw [maximalIdeal_infty_eq_span_t k]
    exact Ideal.mem_span_singleton_self (tA k)
  have ht : t ∈ P := hmap (Ideal.mem_map_of_mem (algebraMap A∞ S∞) htA)
  have heq := infinityZInt_equation k F
  have hz2 : z ^ 2 ∈ P := by
    rw [show z ^ 2 = t - t ^ 3 * z by linear_combination heq]
    exact P.sub_mem ht (P.mul_mem_right _ (P.pow_mem_of_mem ht 3 (by norm_num)))
  have hz : z ∈ P := v.isPrime.mem_of_pow_mem 2 hz2
  have ht2 : t ∈ P ^ 2 := by
    rw [pow_two]
    have hzz : z ^ 2 ∈ P * P := by
      simpa [pow_two] using Ideal.mul_mem_mul hz hz
    have htz : t ^ 3 * z ∈ P * P :=
      Ideal.mul_mem_mul (P.pow_mem_of_mem ht 3 (by norm_num)) hz
    rw [show t = z ^ 2 + t ^ 3 * z by linear_combination -heq]
    exact (P * P).add_mem hzz htz
  rw [maximalIdeal_infty_eq_span_t k, Ideal.map_span, Set.image_singleton, Ideal.span_le]
  rintro _ rfl
  exact ht2
lemma infinity_ramificationIdx_eq_two
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    (IsLocalRing.maximalIdeal A∞).ramificationIdx' v.asIdeal = 2 := by
  let p := IsLocalRing.maximalIdeal A∞
  let P := v.asIdeal
  have hle2 : Ideal.map (algebraMap A∞ S∞) p ≤ P ^ 2 :=
    infinity_map_maximalIdeal_le_sq k F v
  have hpP : Ideal.map (algebraMap A∞ S∞) p ≤ P :=
    hle2.trans (Ideal.pow_le_self (by omega))
  have hne1 : p.ramificationIdx' P ≠ 1 :=
    (Ideal.ramificationIdx'_ne_one_iff hpP).2 hle2
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  have hunder : P.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  have : P.LiesOver p := ⟨hunder.symm⟩
  have hne0 : p.ramificationIdx' P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (S := S∞) P hp0
  have hle : p.ramificationIdx' P ≤ Module.finrank k⟮X⟯ F :=
    Ideal.ramificationIdx_le_finrank (S := S∞) (K := k⟮X⟯) (L := F) P
  rw [finrank_ratFunc_eq_two k F] at hle
  change p.ramificationIdx' P = 2
  omega
lemma infinity_sum_ramification_inertia :
    let p := IsLocalRing.maximalIdeal A∞
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S∞,
      p.ramificationIdx' P * p.inertiaDeg' P = 2 := by
  dsimp
  have hp0 : IsLocalRing.maximalIdeal A∞ ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  rw [Ideal.sum_ramification_inertia S∞ k⟮X⟯ F hp0, finrank_ratFunc_eq_two k F]
lemma infinity_inertiaDeg_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    (IsLocalRing.maximalIdeal A∞).inertiaDeg' v.asIdeal = 1 := by
  let p := IsLocalRing.maximalIdeal A∞
  let P := v.asIdeal
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  have hunder : P.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  have : P.LiesOver p := ⟨hunder.symm⟩
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := P)).2
      ⟨v.isPrime, (show P.LiesOver p from inferInstance)⟩
  let g : Ideal S∞ → ℕ := fun Q => p.ramificationIdx' Q * p.inertiaDeg' Q
  have hsum : (∑ Q ∈ IsDedekindDomain.primesOverFinset p S∞, g Q) = 2 := by
    simpa [g] using infinity_sum_ramification_inertia k F
  have hterm : g P ≤ 2 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ hP]
    omega
  have he : p.ramificationIdx' P = 2 := infinity_ramificationIdx_eq_two k F v
  have hfpos : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
  dsimp [g] at hterm
  rw [he] at hterm
  change p.inertiaDeg' P = 1
  omega
lemma infinity_heightOne_unique
    (v w : IsDedekindDomain.HeightOneSpectrum S∞) : v = w := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  let p := IsLocalRing.maximalIdeal A∞
  let P := v.asIdeal
  let Q := w.asIdeal
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  have hPunder : P.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  have hQunder : Q.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ Q)
  have : P.LiesOver p := ⟨hPunder.symm⟩
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := P)).2
      ⟨v.isPrime, (show P.LiesOver p from inferInstance)⟩
  have : Q.LiesOver p := ⟨hQunder.symm⟩
  have hQ : Q ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := Q)).2
      ⟨w.isPrime, (show Q.LiesOver p from inferInstance)⟩
  by_contra hne
  let g : Ideal S∞ → ℕ := fun R => p.ramificationIdx' R * p.inertiaDeg' R
  let Fs := IsDedekindDomain.primesOverFinset p S∞
  have hsum : Fs.sum g = 2 := by
    simpa [Fs, g] using infinity_sum_ramification_inertia k F
  have hQerase : Q ∈ Fs.erase P := Finset.mem_erase.2 ⟨Ne.symm hne, hQ⟩
  have hQle : g Q ≤ (Fs.erase P).sum g :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hQerase
  have hdecomp : (Fs.erase P).sum g + g P = 2 := by
    calc
      (Fs.erase P).sum g + g P = Fs.sum g := Finset.sum_erase_add Fs g hP
      _ = 2 := hsum
  have heP : p.ramificationIdx' P = 2 := infinity_ramificationIdx_eq_two k F v
  have heQ : p.ramificationIdx' Q = 2 := infinity_ramificationIdx_eq_two k F w
  have hfP : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
  have hfQ : 0 < p.inertiaDeg' Q := Ideal.inertiaDeg'_pos p Q
  dsimp [g] at hQle hdecomp
  rw [heP] at hdecomp
  rw [heQ] at hQle
  omega
def infinityHeightOne : IsDedekindDomain.HeightOneSpectrum S∞ := by
  let p := IsLocalRing.maximalIdeal A∞
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  let hex := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S∞) p
  let P : Ideal S∞ := Classical.choose hex
  have hP : P.IsMaximal ∧ P.LiesOver p := Classical.choose_spec hex
  have : P.LiesOver p := hP.2
  exact ⟨P, hP.1.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩
def infinityPlace : PlaceA k F := Sum.inr (infinityHeightOne k F)
theorem infinityPlace_deg_one : placeDegree k F (infinityPlace k F) = 1 := by
  rw [infinityPlace, placeDegree_infinite_eq_inertiaDeg]
  have hunder : (infinityHeightOne k F).asIdeal.under A∞ =
      IsLocalRing.maximalIdeal A∞ :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.under A∞ (infinityHeightOne k F).asIdeal)
  rw [hunder]
  exact infinity_inertiaDeg_eq_one k F (infinityHeightOne k F)
theorem eq_infinityPlace (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    (Sum.inr v : PlaceA k F) = infinityPlace k F :=
  congrArg Sum.inr (infinity_heightOne_unique k F v _)
end
end WeilConjectures.Bridge.Hyperelliptic
end
section
open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc WithZero
namespace WeilConjectures.Bridge.Hyperelliptic
noncomputable section
variable (k : Type*) [Field k]
variable (F : Type*) [Field F] [Algebra (HypRing k) F] [IsFractionRing (HypRing k) F]
variable [Algebra k[X] F] [IsScalarTower k[X] (HypRing k) F]
  [Algebra k⟮X⟯ F] [IsScalarTower k[X] k⟮X⟯ F]
  [_root_.FunctionField k F] [Algebra.IsSeparable k⟮X⟯ F]
  [Algebra k F] [IsScalarTower k k[X] F]
omit [_root_.FunctionField k F] [Algebra.IsSeparable k⟮X⟯ F] [Algebra k F]
  [IsScalarTower k k[X] F] in
lemma yF_ne_zero : yF k F ≠ 0 := by
  intro h
  exact yF_notMem_range k F ⟨0, by simpa using h.symm⟩
lemma valuation_XK_infinity :
    placeValuation k F (infinityPlace k F) (XK k F) = WithZero.exp (2 : ℤ) := by
  have h := placeValuation_eq_exp_neg_principalDivisor k F
    (Additive.ofMul (Units.mk0 (XK k F) (XK_ne_zero k F))) (infinityPlace k F)
  rw [show infinityPlace k F = Sum.inr (infinityHeightOne k F) from rfl,
    principalDivisorA_XK_at_infinite,
    show ramIdxInfty k F (infinityHeightOne k F).asIdeal = 2 by
      exact infinity_ramificationIdx_eq_two k F _] at h
  change placeValuation k F (Sum.inr (infinityHeightOne k F)) (XK k F) =
    WithZero.exp (-(-((2 : ℕ) : ℤ))) at h
  norm_num at h
  simpa only [infinityPlace] using h
lemma yF_order_at_infinity :
    principalDivisorA k F
      (Additive.ofMul (Units.mk0 (yF k F) (yF_ne_zero k F))) (infinityPlace k F) = -5 := by
  let V := placeValuation k F (infinityPlace k F)
  let y := yF k F
  let n := principalDivisorA k F
    (Additive.ofMul (Units.mk0 y (yF_ne_zero k F))) (infinityPlace k F)
  have hvy : V y = WithZero.exp (-n) :=
    placeValuation_eq_exp_neg_principalDivisor k F
      (Additive.ofMul (Units.mk0 y (yF_ne_zero k F))) (infinityPlace k F)
  have hsum : V (y ^ 2 + y) = WithZero.exp (10 : ℤ) := by
    rw [yF_equation, map_pow, valuation_XK_infinity, ← WithZero.exp_nsmul]
    norm_num
  by_cases hn : 0 < -n
  · have hy2 : V (y ^ 2) = WithZero.exp (-2 * n) := by
      rw [map_pow, hvy, ← WithZero.exp_nsmul]
      congr 1
      ring
    have hlt : V y < V (y ^ 2) := by
      rw [hy2, hvy]
      exact WithZero.exp_lt_exp.mpr (by omega)
    rw [V.map_add_eq_of_lt_left hlt, hy2] at hsum
    have := WithZero.exp_injective hsum
    change n = -5
    omega
  · exfalso
    have hy1 : V y ≤ 1 := by
      rw [hvy, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hle : V (y ^ 2 + y) ≤ 1 :=
      (V.map_add _ _).trans (max_le (by rw [map_pow]; exact pow_le_one₀ zero_le hy1) hy1)
    rw [hsum, ← WithZero.exp_zero] at hle
    exact absurd (WithZero.exp_le_exp.mp hle) (by norm_num)
def infinityDivisor : DivisorA k F := Finsupp.single (infinityPlace k F) 1
omit [Algebra k F] [IsScalarTower k k[X] F] in
lemma deg_infinityDivisor : deg k F (infinityDivisor k F) = 1 := by
  rw [infinityDivisor, deg_single, infinityPlace_deg_one k F]
  norm_num
omit [Algebra (HypRing k) F] [IsFractionRing (HypRing k) F]
  [IsScalarTower k[X] (HypRing k) F] [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] [Algebra k F] [IsScalarTower k k[X] F] in
lemma infinityDivisor_nonneg : 0 ≤ infinityDivisor k F := by
  classical
  intro v
  rw [infinityDivisor, Finsupp.single_apply]
  split <;> simp
lemma polarDivisor_XK_eq_two_infinity :
    polarDivisor k F (XK k F) = 2 • infinityDivisor k F := by
  classical
  ext v
  rcases v with v | v
  · rw [polarDivisor_XK_zero_at_finite]
    have hne : infinityPlace k F ≠ Sum.inl v := by intro h; cases h
    simp [infinityDivisor, hne]
  · have hv : v = infinityHeightOne k F := infinity_heightOne_unique k F _ _
    subst v
    rw [polarDivisor_XK_at_infinite]
    have he : ramIdxInfty k F (infinityHeightOne k F).asIdeal = 2 :=
      infinity_ramificationIdx_eq_two k F _
    rw [he]
    simp [infinityDivisor, infinityPlace]
omit [IsFractionRing (HypRing k) F] [Algebra k⟮X⟯ F] [IsScalarTower k[X] k⟮X⟯ F]
  [_root_.FunctionField k F] [Algebra.IsSeparable k⟮X⟯ F] [Algebra k F]
  [IsScalarTower k k[X] F] in
lemma yF_mem_ringOfIntegers : ∃ a : ringOfIntegers k F, (a : F) = yF k F := by
  have hyintR : _root_.IsIntegral k[X] (yR k) := Algebra.IsIntegral.isIntegral (yR k)
  have hyintK : _root_.IsIntegral k[X] (yF k F) := by
    simpa [yF] using hyintR.map (IsScalarTower.toAlgHom k[X] (HypRing k) F)
  exact ⟨⟨yF k F, hyintK⟩, rfl⟩
omit [Algebra k F] [IsScalarTower k k[X] F] in
lemma polarDivisor_yF_zero_at_finite
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F)) :
    polarDivisor k F (yF k F) (Sum.inl v) = 0 := by
  have hy0 := yF_ne_zero k F
  obtain ⟨a, ha⟩ := yF_mem_ringOfIntegers k F
  have ha0 : a ≠ 0 := fun ha0 => hy0 (by simpa [ha] using congrArg Subtype.val ha0)
  have hprincipal :
      0 ≤ principalDivisorA k F
        (Additive.ofMul (Units.mk0 (yF k F) hy0)) (Sum.inl v) := by
    simpa [ha] using
      principalDivisorA_nonneg_at_finite_of_mem_ringOfIntegers (k := k) (K := F) ha0 v
  unfold polarDivisor
  simp only [dif_neg hy0, Finsupp.sup_apply]
  exact max_eq_right (neg_nonpos.mpr hprincipal)
lemma polarDivisor_yF_eq_five_infinity :
    polarDivisor k F (yF k F) = 5 • infinityDivisor k F := by
  classical
  ext v
  rcases v with v | v
  · rw [polarDivisor_yF_zero_at_finite]
    have hne : infinityPlace k F ≠ Sum.inl v := by intro h; cases h
    simp [infinityDivisor, hne]
  · have hv : v = infinityHeightOne k F := infinity_heightOne_unique k F _ _
    subst v
    have hy0 := yF_ne_zero k F
    have hord := yF_order_at_infinity k F
    change polarDivisor k F (yF k F) (infinityPlace k F) = _
    unfold polarDivisor
    rw [dif_neg hy0]
    change max (-principalDivisorA k F
      (Additive.ofMul (Units.mk0 (yF k F) hy0)) (infinityPlace k F)) 0 = _
    rw [hord]
    simp [infinityDivisor, infinityPlace]
lemma valuation_aeval_XK (p : k[X]) (hp : p ≠ 0) :
    placeValuation k F (infinityPlace k F) (Polynomial.aeval (XK k F) p) =
      WithZero.exp (2 * p.natDegree : ℤ) := by
  let V := placeValuation k F (infinityPlace k F)
  have : V.IsTrivialOn k :=
    ⟨fun a ha => by
      simpa [V] using placeValuation_algebraMap_eq_one k F (infinityPlace k F) (Units.mk0 a ha)⟩
  have hvx := valuation_XK_infinity k F
  rw [Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
    (XK k F) (by rw [hvx, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)) hp,
    hvx, ← WithZero.exp_nsmul]
  congr 1
  ring
lemma valuation_yF_infinity :
    placeValuation k F (infinityPlace k F) (yF k F) = WithZero.exp (5 : ℤ) := by
  have hy := placeValuation_eq_exp_neg_principalDivisor k F
    (Additive.ofMul (Units.mk0 (yF k F) (yF_ne_zero k F))) (infinityPlace k F)
  rw [yF_order_at_infinity k F] at hy
  change placeValuation k F (infinityPlace k F) (yF k F) = WithZero.exp (-(-5 : ℤ)) at hy
  norm_num at hy
  exact hy
lemma valuation_aeval_XK_mul_yF (q : k[X]) (hq : q ≠ 0) :
    placeValuation k F (infinityPlace k F) (Polynomial.aeval (XK k F) q * yF k F) =
      WithZero.exp (2 * q.natDegree + 5 : ℤ) := by
  rw [map_mul, valuation_aeval_XK k F q hq, valuation_yF_infinity, ← WithZero.exp_add]
lemma ell_nsmul_infinity_ge_add (r a b : ℕ)
    (ha : ∀ j : Fin a, 2 * (j : ℕ) ≤ r)
    (hb : ∀ j : Fin b, 2 * (j : ℕ) + 5 ≤ r) :
    a + b ≤ Chart.ell k F (r • infinityDivisor k F) := by
  classical
  have hDnn := infinityDivisor_nonneg k F
  let basis := basisRatFunc k F
  let g : Fin a ⊕ Fin b → Fin 2 × Fin (r + 1)
    | Sum.inl j => ⟨0, ⟨j, by have := ha j; omega⟩⟩
    | Sum.inr j => ⟨1, ⟨j, by have := hb j; omega⟩⟩
  have hg : Function.Injective g := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · congr
      exact Fin.ext (congrArg (fun z => z.2.val) hij)
    · have := congrArg (fun z => z.1.val) hij
      simp [g] at this
    · have := congrArg (fun z => z.1.val) hij
      simp [g] at this
    · congr
      exact Fin.ext (congrArg (fun z => z.2.val) hij)
  let f : Fin a ⊕ Fin b → F := fun i =>
    basis (g i).1 * (XK k F) ^ ((g i).2 : ℕ)
  have hlin : LinearIndependent k f := by
    exact (linearIndependent_basis_smul_XK_pow (k := k) (K := F) basis).comp g hg
  have hmem : ∀ i, f i ∈ Chart.RRspace k F (r • infinityDivisor k F) := by
    intro i
    rw [Chart.mem_RRspace_iff]
    rcases i with j | j
    · have hx := memRRspace_smul_polar (k := k) (K := F) (XK_ne_zero k F) (j : ℕ)
      have hx' : Chart.memRRspace k F (((j : ℕ) * 2) • infinityDivisor k F)
          ((XK k F) ^ (j : ℕ)) := by
        convert hx using 1
        ext v
        rw [polarDivisor_XK_eq_two_infinity k F]
        simp only [Finsupp.nsmul_apply]
        ring
      have hle : ((j : ℕ) * 2) • infinityDivisor k F ≤ r • infinityDivisor k F := by
        intro v
        simp only [Finsupp.nsmul_apply]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simpa [mul_comm] using ha j))
          (hDnn v)
      simpa [f, g, basis] using
        (memRRspace.memRRspace_mono (k := k) (K := F) hle hx')
    · have hx := memRRspace_smul_polar (k := k) (K := F) (XK_ne_zero k F) (j : ℕ)
      have hy := memRRspace_polarDivisor_of_ne_zero (k := k) (K := F) (yF_ne_zero k F)
      have hmul := memRRspace.mul_mem (k := k) (K := F) hx hy
      have hxy : Chart.memRRspace k F (((j : ℕ) * 2 + 5) • infinityDivisor k F)
          ((XK k F) ^ (j : ℕ) * yF k F) := by
        convert hmul using 1
        ext v
        rw [polarDivisor_XK_eq_two_infinity k F, polarDivisor_yF_eq_five_infinity k F]
        simp only [Finsupp.nsmul_apply, Finsupp.add_apply]
        ring
      have hle : ((j : ℕ) * 2 + 5) • infinityDivisor k F ≤ r • infinityDivisor k F := by
        intro v
        simp only [Finsupp.nsmul_apply]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simpa [mul_comm] using hb j))
          (hDnn v)
      simpa [f, g, basis, mul_comm] using
        (memRRspace.memRRspace_mono (k := k) (K := F) hle hxy)
  have hspan : Submodule.span k (Set.range f) ≤ Chart.RRspace k F (r • infinityDivisor k F) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hcard : a + b = Module.finrank k (Submodule.span k (Set.range f)) := by
    rw [finrank_span_eq_card hlin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  rw [hcard]
  exact Submodule.finrank_mono hspan
lemma ell_nsmul_infinity_ge (r : ℕ) : r ≤ Chart.ell k F (r • infinityDivisor k F) + 1 := by
  by_cases heven : r % 2 = 0
  · let m := r / 2
    by_cases hm : m ≤ 1
    · have h := ell_nsmul_infinity_ge_add k F r (m + 1) 0
          (fun j => by have := j.isLt; omega) (fun j => j.elim0)
      omega
    · have h := ell_nsmul_infinity_ge_add k F r (m + 1) (m - 2)
          (fun j => by have := j.isLt; omega)
          (fun j => by have := j.isLt; omega)
      omega
  · let m := r / 2
    by_cases hm : m = 0
    · have h := ell_nsmul_infinity_ge_add k F r 1 0
          (fun j => by have := j.isLt; omega) (fun j => j.elim0)
      omega
    · have h := ell_nsmul_infinity_ge_add k F r (m + 1) (m - 1)
          (fun j => by have := j.isLt; omega)
          (fun j => by have := j.isLt; omega)
      omega
variable [NeZero (5 : k)]
def coordinateRingEquivIntegers : HypRing k ≃ₐ[k[X]] ringOfIntegers k F :=
  IsIntegralClosure.equiv k[X] (HypRing k) F (ringOfIntegers k F)
lemma exists_aeval_of_integral (f : F)
    (hf : ∀ v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F),
      placeValuation k F (Sum.inl v) f ≤ 1) :
    ∃ p q : k[X], Polynomial.aeval (XK k F) p + Polynomial.aeval (XK k F) q * yF k F = f := by
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := ringOfIntegers k F) F f hf
  let e := coordinateRingEquivIntegers k F
  let r : HypRing k := e.symm a
  have hrK : algebraMap (HypRing k) F r = f := by
    have hemb := IsIntegralClosure.algebraMap_equiv k[X] (HypRing k) F
      (ringOfIntegers k F) r
    change algebraMap (ringOfIntegers k F) F ((coordinateRingEquivIntegers k F) r) =
      algebraMap (HypRing k) F r at hemb
    calc
      algebraMap (HypRing k) F r = algebraMap (ringOfIntegers k F) F (e r) := hemb.symm
      _ = (a : F) := by rw [e.apply_symm_apply]; rfl
      _ = f := ha
  obtain ⟨p, q, hpq⟩ := exists_eq_add_mul_yR k r
  refine ⟨p, q, ?_⟩
  rw [← algebraMap_polynomial_eq_aeval_XK, ← algebraMap_polynomial_eq_aeval_XK, ← hrK, ← hpq,
    map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, yF]
lemma mem_span_of_mem_RRspace_three (f : F)
    (hf : f ∈ Chart.RRspace k F (3 • infinityDivisor k F)) :
    ∃ a b : k, algebraMap k F a + algebraMap k F b * XK k F = f := by
  have hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F),
      placeValuation k F (Sum.inl v) f ≤ 1 := fun v => by
    have hv := (Chart.mem_RRspace_iff k F _ f).mp hf (Sum.inl v)
    have hne : infinityPlace k F ≠ Sum.inl v := by intro h; cases h
    simpa [infinityDivisor, Finsupp.single_apply, hne] using hv
  obtain ⟨p, q, hfdecomp⟩ := exists_aeval_of_integral k F f hfin
  have hvinf := (Chart.mem_RRspace_iff k F _ f).mp hf (infinityPlace k F)
  have hD : (3 • infinityDivisor k F) (infinityPlace k F) = 3 := by
    simp [infinityDivisor]
  rw [hD] at hvinf
  let V := placeValuation k F (infinityPlace k F)
  by_cases hq : q = 0
  · subst q
    simp only [map_zero, zero_mul, add_zero] at hfdecomp
    by_cases hp : p = 0
    · subst p
      exact ⟨0, 0, by simpa using hfdecomp⟩
    · have hpval := valuation_aeval_XK k F p hp
      have hvp_le : WithZero.exp (2 * p.natDegree : ℤ) ≤ WithZero.exp (3 : ℤ) := by
        rw [← hpval, hfdecomp]
        exact hvinf
      have hpdeg : p.natDegree ≤ 1 := by
        have := WithZero.exp_le_exp.mp hvp_le
        omega
      refine ⟨p.coeff 0, p.coeff 1, ?_⟩
      rw [← hfdecomp, Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg]
      simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
      ring
  · exfalso
    have hqval := valuation_aeval_XK_mul_yF k F q hq
    have hbig : WithZero.exp (5 : ℤ) ≤ V f := by
      rw [← hfdecomp]
      by_cases hp : p = 0
      · subst p
        rw [map_zero, zero_add, hqval]
        exact WithZero.exp_le_exp.mpr (by omega)
      · have hpval := valuation_aeval_XK k F p hp
        have hne : (2 * p.natDegree : ℤ) ≠ 2 * q.natDegree + 5 := by omega
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · rw [V.map_add_eq_of_lt_right (by rw [hpval, hqval]; exact WithZero.exp_lt_exp.mpr hlt),
            hqval]
          exact WithZero.exp_le_exp.mpr (by omega)
        · rw [V.map_add_eq_of_lt_left (by rw [hpval, hqval]; exact WithZero.exp_lt_exp.mpr hgt),
            hpval]
          exact WithZero.exp_le_exp.mpr (by omega)
    have := WithZero.exp_le_exp.mp (hbig.trans hvinf)
    omega
lemma ell_three_infinity_le : Chart.ell k F (3 • infinityDivisor k F) ≤ 2 := by
  let φ : (Fin 2 → k) →ₗ[k] F :=
    (Fintype.linearCombination k ![(1 : F), XK k F])
  have hle : Chart.RRspace k F (3 • infinityDivisor k F) ≤ LinearMap.range φ := by
    intro f hf
    obtain ⟨a, b, hab⟩ := mem_span_of_mem_RRspace_three k F f hf
    refine ⟨![a, b], ?_⟩
    rw [← hab]
    simp [φ, Fintype.linearCombination_apply, Fin.sum_univ_two, Algebra.smul_def]
  change Module.finrank k (Chart.RRspace k F (3 • infinityDivisor k F)) ≤ 2
  calc
    Module.finrank k (Chart.RRspace k F (3 • infinityDivisor k F))
        ≤ Module.finrank k (LinearMap.range φ) := Submodule.finrank_mono hle
    _ ≤ Module.finrank k (Fin 2 → k) := LinearMap.finrank_range_le φ
    _ = 2 := by simp
variable [IsFullConstantField k F]
theorem chart_genus_eq_two : FunctionField.Chart.genus k F = 2 := by
  let B := infinityDivisor k F
  have hdegB : deg k F B = 1 := deg_infinityDivisor k F
  have hmono : ∀ r : ℕ, FunctionField.Chart.defect k F (0 + r • B) ≤ 2 := by
    intro r
    have hell := ell_nsmul_infinity_ge k F r
    have hdeg : deg k F (r • B) = r := by
      rw [deg_nsmul, hdegB]
      norm_num
    dsimp only [FunctionField.Chart.defect]
    rw [zero_add, hdeg]
    have : (r : ℤ) ≤ FunctionField.Chart.ell k F (r • B) + 1 := by exact_mod_cast hell
    omega
  have hgrow : ∀ m : ℤ, ∃ r : ℕ, m ≤ FunctionField.Chart.ell k F (0 + r • B) := by
    intro m
    refine ⟨(m + 1).toNat, ?_⟩
    rw [zero_add]
    have h := ell_nsmul_infinity_ge k F (m + 1).toNat
    have : ((m + 1).toNat : ℤ) ≤ FunctionField.Chart.ell k F ((m + 1).toNat • B) + 1 := by
      exact_mod_cast h
    omega
  have hall : ∀ D : DivisorA k F, FunctionField.Chart.defect k F D ≤ 2 :=
    defect_le_of_family (k := k) (K := F) B 0 2 hmono hgrow
  have hgen_le : FunctionField.Chart.genus k F ≤ 2 := by
    obtain ⟨D, hD⟩ := exists_defect_eq (k := k) (K := F)
    have h := hall D
    rw [hD] at h
    exact_mod_cast h
  have hdef3 : 2 ≤ FunctionField.Chart.defect k F (3 • B) := by
    have h3 := ell_three_infinity_le k F
    dsimp only [FunctionField.Chart.defect]
    rw [deg_nsmul, hdegB]
    have : (FunctionField.Chart.ell k F (3 • B) : ℤ) ≤ 2 := by exact_mod_cast h3
    omega
  have hgen_ge : 2 ≤ FunctionField.Chart.genus k F := by
    have h := defect_le k F (3 • B)
    exact_mod_cast hdef3.trans h
  omega
theorem genus_eq_two : FunctionField.genus k F = 2 :=
  (FunctionField.genus_eq_genusChart k F).trans (chart_genus_eq_two k F)
theorem genusFF_eq_two [PerfectField k] :
    AlgebraicCurve.genusFF k F = 2 :=
  (WeilConjectures.Bridge.genusFF_eq_genus k F).trans (genus_eq_two k F)
end
end WeilConjectures.Bridge.Hyperelliptic
end
section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open FunctionField
open FunctionField.Chart
open Polynomial
open scoped Polynomial RatFunc WithZero
namespace WeilConjectures.Bridge.Hyperelliptic
noncomputable section
section Evaluation
variable {k : Type*} [Field k]
def ev (a b : k) (h : b ^ 2 + b = a ^ 5) : HypRing k →+* k :=
  AdjoinRoot.lift (Polynomial.evalRingHom a) b (by
    simp [hypPoly, eval₂_sub, eval₂_add, eval₂_pow, eval₂_C, h])
lemma ev_of (a b : k) (h : b ^ 2 + b = a ^ 5) (p : k[X]) :
    ev a b h (algebraMap k[X] (HypRing k) p) = p.eval a := by
  rw [ev, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  rfl
lemma ev_algebraMap (a b : k) (h : b ^ 2 + b = a ^ 5) (c : k) :
    ev a b h (algebraMap k (HypRing k) c) = c := by
  rw [IsScalarTower.algebraMap_apply k k[X] (HypRing k), ev_of]
  simp
lemma ev_xR (a b : k) (h : b ^ 2 + b = a ^ 5) : ev a b h (xR k) = a := by
  rw [xR, ev_of, eval_X]
lemma ev_yR (a b : k) (h : b ^ 2 + b = a ^ 5) : ev a b h (yR k) = b := by
  rw [ev, yR, AdjoinRoot.lift_root]
lemma xR_sub_ne_zero (a : k) : xR k - algebraMap k (HypRing k) a ≠ 0 := by
  rw [xR, IsScalarTower.algebraMap_apply k k[X] (HypRing k), ← map_sub]
  intro h
  have := algebraMap_injective k (h.trans (map_zero _).symm)
  exact X_sub_C_ne_zero a (by simpa using this)
def pointIdeal (a b : k) : Ideal (HypRing k) :=
  Ideal.span {xR k - algebraMap k (HypRing k) a, yR k - algebraMap k (HypRing k) b}
lemma algebraMap_sub_eval_mem (a b : k) (p : k[X]) :
    algebraMap k[X] (HypRing k) p - algebraMap k (HypRing k) (p.eval a) ∈ pointIdeal a b := by
  obtain ⟨g, hg⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := a) (p := p)
  have : algebraMap k[X] (HypRing k) p - algebraMap k (HypRing k) (p.eval a) =
      (xR k - algebraMap k (HypRing k) a) * algebraMap k[X] (HypRing k) g := by
    rw [IsScalarTower.algebraMap_apply k k[X] (HypRing k) (p.eval a),
      IsScalarTower.algebraMap_apply k k[X] (HypRing k) a, xR, ← map_sub, ← map_sub,
      ← map_mul]
    exact congrArg _ hg
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
lemma sub_ev_mem (a b : k) (h : b ^ 2 + b = a ^ 5) (r : HypRing k) :
    r - algebraMap k (HypRing k) (ev a b h r) ∈ pointIdeal a b := by
  obtain ⟨p, q, rfl⟩ := exists_eq_add_mul_yR k r
  have hy : yR k - algebraMap k (HypRing k) b ∈ pointIdeal a b :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hp := algebraMap_sub_eval_mem a b p
  have hq := algebraMap_sub_eval_mem a b q
  rw [map_add, map_mul, ev_of, ev_of, ev_yR]
  have : algebraMap k[X] (HypRing k) p + algebraMap k[X] (HypRing k) q * yR k -
      algebraMap k (HypRing k) (p.eval a + q.eval a * b) =
      (algebraMap k[X] (HypRing k) p - algebraMap k (HypRing k) (p.eval a)) +
        algebraMap k[X] (HypRing k) q * (yR k - algebraMap k (HypRing k) b) +
        algebraMap k (HypRing k) b *
          (algebraMap k[X] (HypRing k) q - algebraMap k (HypRing k) (q.eval a)) := by
    rw [map_add, map_mul]
    ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.add_mem _ hp (Ideal.mul_mem_left _ _ hy))
    (Ideal.mul_mem_left _ _ hq)
lemma pointIdeal_le_ker (a b : k) (h : b ^ 2 + b = a ^ 5) :
    pointIdeal a b ≤ RingHom.ker (ev a b h) := by
  rw [pointIdeal, Ideal.span_le]
  rintro _ (rfl | rfl)
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, ev_xR, ev_algebraMap, sub_self]
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, ev_yR, ev_algebraMap, sub_self]
lemma le_of_pointIdeal_le (a b : k) (h : b ^ 2 + b = a ^ 5) {P Q : Ideal (HypRing k)}
    (hP : P ≠ ⊤) (hQ : pointIdeal a b ≤ Q) : P ≤ Q ∨ ¬ pointIdeal a b ≤ P := by
  by_cases hIP : pointIdeal a b ≤ P
  · left
    intro r hr
    have hev : algebraMap k (HypRing k) (ev a b h r) ∈ P := by
      have := P.sub_mem hr (hIP (sub_ev_mem a b h r))
      rwa [sub_sub_cancel] at this
    have h0 : ev a b h r = 0 := by
      by_contra hne
      exact hP (P.eq_top_of_isUnit_mem hev ((isUnit_iff_ne_zero.mpr hne).map _))
    have := hQ (sub_ev_mem a b h r)
    rwa [h0, map_zero, sub_zero] at this
  · exact Or.inr hIP
lemma ev_surjective (a b : k) (h : b ^ 2 + b = a ^ 5) : Function.Surjective (ev a b h) :=
  fun c => ⟨algebraMap k (HypRing k) c, ev_algebraMap a b h c⟩
lemma ker_ev_isMaximal (a b : k) (h : b ^ 2 + b = a ^ 5) : (RingHom.ker (ev a b h)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (ev_surjective a b h)
lemma ker_ev_ne_bot (a b : k) (h : b ^ 2 + b = a ^ 5) : RingHom.ker (ev a b h) ≠ ⊥ := by
  intro hbot
  apply xR_sub_ne_zero (k := k) a
  rw [← Ideal.mem_bot, ← hbot]
  exact pointIdeal_le_ker a b h (Ideal.subset_span (Set.mem_insert _ _))
lemma exists_point_of_isMaximal [IsAlgClosed k] (P : Ideal (HypRing k)) [P.IsMaximal] :
    ∃ a b : k, b ^ 2 + b = a ^ 5 ∧ pointIdeal a b ≤ P := by
  let L := HypRing k ⧸ P
  letI : Field L := Ideal.Quotient.field P
  haveI : Algebra.FiniteType k (HypRing k) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k k[X]) inferInstance
  haveI : Algebra.FiniteType k L := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k (HypRing k)) inferInstance
  haveI : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  haveI : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    (Ideal.Quotient.mk P (xR k))
  obtain ⟨b, hb⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    (Ideal.Quotient.mk P (yR k))
  have hmk : ∀ c : k, Ideal.Quotient.mk P (algebraMap k (HypRing k) c) = algebraMap k L c :=
    fun c => rfl
  have heq : b ^ 2 + b = a ^ 5 := by
    apply (algebraMap k L).injective
    have := congrArg (Ideal.Quotient.mk P) (yR_sq_add_yR k)
    rw [map_add, map_pow, map_pow, ← ha, ← hb] at this
    simpa using this
  refine ⟨a, b, heq, ?_⟩
  rw [pointIdeal, Ideal.span_le]
  rintro _ (rfl | rfl) <;> apply Ideal.Quotient.eq_zero_iff_mem.mp <;>
    rw [map_sub, sub_eq_zero, hmk]
  · exact ha.symm
  · exact hb.symm
end Evaluation
variable (k : Type*) [Field k]
variable (F : Type*) [Field F] [Algebra (HypRing k) F] [IsFractionRing (HypRing k) F]
variable [Algebra k[X] F] [IsScalarTower k[X] (HypRing k) F]
  [Algebra k⟮X⟯ F] [IsScalarTower k[X] k⟮X⟯ F]
  [_root_.FunctionField k F] [Algebra.IsSeparable k⟮X⟯ F]
  [Algebra k F] [IsScalarTower k k[X] F] [NeZero (5 : k)]
local instance instHypConstantsTowerPts : IsScalarTower k (HypRing k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] F,
      IsScalarTower.algebraMap_apply k k[X] (HypRing k),
      ← IsScalarTower.algebraMap_apply k[X] (HypRing k) F]
omit [NeZero (5 : k)] [_root_.FunctionField k F] [Algebra.IsSeparable k⟮X⟯ F] in
lemma algebraMap_xR_sub (a : k) :
    algebraMap (HypRing k) F (xR k - algebraMap k (HypRing k) a) =
      XK k F - algebraMap k F a := by
  rw [map_sub, xF_eq_XK, ← IsScalarTower.algebraMap_apply]
omit [NeZero (5 : k)] [IsFractionRing (HypRing k) F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] in
lemma algebraMap_yR_sub (b : k) :
    algebraMap (HypRing k) F (yR k - algebraMap k (HypRing k) b) =
      yF k F - algebraMap k F b := by
  rw [map_sub, ← IsScalarTower.algebraMap_apply]
  rfl
lemma placeValuation_lt_one_iff (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F))
    (r : HypRing k) :
    placeValuation k F (Sum.inl v) (algebraMap (HypRing k) F r) < 1 ↔
      r ∈ v.asIdeal.comap (coordinateRingEquivIntegers k F).toRingHom := by
  have hemb := IsIntegralClosure.algebraMap_equiv k[X] (HypRing k) F (ringOfIntegers k F) r
  change algebraMap (ringOfIntegers k F) F (coordinateRingEquivIntegers k F r) =
    algebraMap (HypRing k) F r at hemb
  rw [Ideal.mem_comap, ← hemb]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v _
def ChartCentred (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F)) (a b : k) :
    Prop :=
  placeValuation k F (Sum.inl v) (XK k F - algebraMap k F a) < 1 ∧
    placeValuation k F (Sum.inl v) (yF k F - algebraMap k F b) < 1
lemma chartCentred_iff (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F)) (a b : k) :
    ChartCentred k F v a b ↔
      pointIdeal a b ≤ v.asIdeal.comap (coordinateRingEquivIntegers k F).toRingHom := by
  rw [ChartCentred, ← algebraMap_xR_sub, ← algebraMap_yR_sub, placeValuation_lt_one_iff,
    placeValuation_lt_one_iff, pointIdeal, Ideal.span_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  rfl
lemma comap_ne_top (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F)) :
    v.asIdeal.comap (coordinateRingEquivIntegers k F).toRingHom ≠ ⊤ :=
  (Ideal.IsPrime.comap (coordinateRingEquivIntegers k F).toRingHom (hK := v.isPrime)).ne_top
lemma chartCentred_unique {a b : k} (h : b ^ 2 + b = a ^ 5)
    {v v' : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F)}
    (hv : ChartCentred k F v a b) (hv' : ChartCentred k F v' a b) : v = v' := by
  rw [chartCentred_iff] at hv hv'
  let e := (coordinateRingEquivIntegers k F).toRingEquiv
  have hle : ∀ {P Q : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F)},
      pointIdeal a b ≤ P.asIdeal.comap e.toRingHom →
      pointIdeal a b ≤ Q.asIdeal.comap e.toRingHom →
      P.asIdeal.comap e.toRingHom ≤ Q.asIdeal.comap e.toRingHom := by
    intro P Q hP hQ
    rcases le_of_pointIdeal_le a b h (comap_ne_top k F P) hQ with h' | h'
    · exact h'
    · exact absurd hP h'
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact Ideal.comap_injective_of_surjective _ e.surjective (le_antisymm (hle hv hv') (hle hv' hv))
lemma exists_chartCentred {a b : k} (h : b ^ 2 + b = a ^ 5) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F), ChartCentred k F v a b := by
  let e := (coordinateRingEquivIntegers k F).toRingEquiv
  let u : IsDedekindDomain.HeightOneSpectrum (HypRing k) :=
    ⟨RingHom.ker (ev a b h), (ker_ev_isMaximal a b h).isPrime, ker_ev_ne_bot a b h⟩
  refine ⟨IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e u, ?_⟩
  rw [chartCentred_iff]
  have : (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e u).asIdeal.comap
      e.toRingHom = u.asIdeal := by
    change (u.asIdeal.comap e.symm.toRingHom).comap e.toRingHom = u.asIdeal
    rw [Ideal.comap_comap, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.comap_id]
  change pointIdeal a b ≤ _
  rw [show (coordinateRingEquivIntegers k F).toRingHom = e.toRingHom from rfl, this]
  exact pointIdeal_le_ker a b h
lemma exists_centre_of_finite [IsAlgClosed k]
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F)) :
    ∃ a b : k, b ^ 2 + b = a ^ 5 ∧ ChartCentred k F v a b := by
  let P := v.asIdeal.comap (coordinateRingEquivIntegers k F).toRingHom
  haveI : P.IsPrime := Ideal.IsPrime.comap _ (hK := v.isPrime)
  have hP0 : P ≠ ⊥ := by
    intro hbot
    apply v.ne_bot
    apply Ideal.comap_injective_of_surjective _ (coordinateRingEquivIntegers k F).surjective
    change P = _
    rw [hbot, Ideal.comap_bot_of_injective _ (coordinateRingEquivIntegers k F).injective]
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  obtain ⟨a, b, h, hle⟩ := exists_point_of_isMaximal P
  exact ⟨a, b, h, (chartCentred_iff k F v a b).mpr hle⟩
omit [NeZero (5 : k)] in
lemma placeValuation_XK_le_one (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k F)) :
    placeValuation k F (Sum.inl v) (XK k F) ≤ 1 :=
  Place.finite_X_le_one k F v
omit [NeZero (5 : k)] in
lemma one_lt_placeValuation_XK (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k F)) :
    1 < placeValuation k F (Sum.inr v) (XK k F) := by
  rw [eq_infinityPlace, valuation_XK_infinity, ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by norm_num)
def fltToChart (w : AlgebraicCurve.Place k F) : PlaceA k F :=
  (chartToPlace k F).symm ((WeilConjectures.Bridge.placeEquiv k F).symm w)
omit [NeZero (5 : k)] in
lemma mem_iff_placeValuation (w : AlgebraicCurve.Place k F) (f : F) :
    f ∈ w.toValuationSubring ↔ placeValuation k F (fltToChart k F w) f ≤ 1 := by
  have hw : w = WeilConjectures.Bridge.placeEquiv k F (chartToPlace k F (fltToChart k F w)) := by
    simp [fltToChart]
  conv_lhs => rw [hw]
  rw [WeilConjectures.Bridge.placeEquiv_toValuationSubring, chartToPlace_apply,
    Place.ofChart_toValuationSubring, Valuation.mem_valuationSubring_iff]
def IsInMax (w : AlgebraicCurve.Place k F) (f : F) : Prop :=
  f ∈ w.toValuationSubring ∧ f⁻¹ ∉ w.toValuationSubring
omit [NeZero (5 : k)] in
lemma isInMax_iff (w : AlgebraicCurve.Place k F) {f : F} (hf : f ≠ 0) :
    IsInMax k F w f ↔ placeValuation k F (fltToChart k F w) f < 1 := by
  rw [IsInMax, mem_iff_placeValuation, mem_iff_placeValuation, map_inv₀, not_le,
    one_lt_inv₀ ((Valuation.pos_iff _).mpr hf)]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
def IsCentred (w : AlgebraicCurve.Place k F) (a b : k) : Prop :=
  IsInMax k F w (XK k F - algebraMap k F a) ∧ IsInMax k F w (yF k F - algebraMap k F b)
omit [NeZero (5 : k)] in
lemma XK_sub_ne_zero (a : k) : XK k F - algebraMap k F a ≠ 0 := by
  rw [← algebraMap_xR_sub]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (HypRing k) F)).mpr (xR_sub_ne_zero a)
omit [NeZero (5 : k)] in
lemma yF_sub_ne_zero (b : k) : yF k F - algebraMap k F b ≠ 0 := by
  intro h
  apply yF_notMem_range k F
  refine ⟨algebraMap k[X] k⟮X⟯ (algebraMap k k[X] b), ?_⟩
  rw [← IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F, ← IsScalarTower.algebraMap_apply k k[X] F]
  exact (sub_eq_zero.mp h).symm
omit [NeZero (5 : k)] in
lemma isCentred_iff_chart (w : AlgebraicCurve.Place k F) (a b : k) :
    IsCentred k F w a b ↔
      placeValuation k F (fltToChart k F w) (XK k F - algebraMap k F a) < 1 ∧
        placeValuation k F (fltToChart k F w) (yF k F - algebraMap k F b) < 1 := by
  rw [IsCentred, isInMax_iff k F w (XK_sub_ne_zero k F a), isInMax_iff k F w (yF_sub_ne_zero k F b)]
omit [NeZero (5 : k)] in
lemma XK_mem_of_isCentred {w : AlgebraicCurve.Place k F} {a b : k} (h : IsCentred k F w a b) :
    XK k F ∈ w.toValuationSubring := by
  have := add_mem h.1.1 (w.algebraMap_mem' a)
  rwa [sub_add_cancel] at this
omit [NeZero (5 : k)] in
lemma fltToChart_eq_inr_iff (w : AlgebraicCurve.Place k F) :
    XK k F ∉ w.toValuationSubring ↔ ∃ v, fltToChart k F w = Sum.inr v := by
  rw [mem_iff_placeValuation, not_le]
  rcases hc : fltToChart k F w with v | v
  · simp only [reduceCtorEq, exists_false, iff_false, not_lt]
    exact placeValuation_XK_le_one k F v
  · simpa using one_lt_placeValuation_XK k F v
theorem eq_of_XK_notMem {w w' : AlgebraicCurve.Place k F} (hw : XK k F ∉ w.toValuationSubring)
    (hw' : XK k F ∉ w'.toValuationSubring) : w = w' := by
  obtain ⟨v, hv⟩ := (fltToChart_eq_inr_iff k F w).mp hw
  obtain ⟨v', hv'⟩ := (fltToChart_eq_inr_iff k F w').mp hw'
  have : fltToChart k F w = fltToChart k F w' := by
    rw [hv, hv', eq_infinityPlace, eq_infinityPlace]
  simpa [fltToChart] using this
theorem exists_XK_notMem : ∃ w : AlgebraicCurve.Place k F, XK k F ∉ w.toValuationSubring := by
  refine ⟨WeilConjectures.Bridge.placeEquiv k F (chartToPlace k F (infinityPlace k F)), ?_⟩
  rw [fltToChart_eq_inr_iff]
  exact ⟨infinityHeightOne k F, by simp only [fltToChart, Equiv.symm_apply_apply]; rfl⟩
theorem eq_of_isCentred {w : AlgebraicCurve.Place k F} {a b a' b' : k}
    (h : IsCentred k F w a b) (h' : IsCentred k F w a' b') : a = a' ∧ b = b' := by
  have hconst : ∀ {f : F} {c c' : k}, IsInMax k F w (f - algebraMap k F c) →
      IsInMax k F w (f - algebraMap k F c') → c = c' := by
    intro f c c' h1 h2
    by_contra hne
    have hu : algebraMap k F (c' - c) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap k F).injective).mpr (sub_ne_zero.mpr (Ne.symm hne))
    have hmem : algebraMap k F (c' - c) ∈ w.toValuationSubring := w.algebraMap_mem' _
    have hinv : (algebraMap k F (c' - c))⁻¹ ∈ w.toValuationSubring := by
      rw [← map_inv₀]
      exact w.algebraMap_mem' _
    have hdiff : algebraMap k F (c' - c) = (f - algebraMap k F c) - (f - algebraMap k F c') := by
      rw [map_sub]; ring
    have hlt : placeValuation k F (fltToChart k F w) (algebraMap k F (c' - c)) < 1 := by
      have h1' := (isInMax_iff k F w (f := f - algebraMap k F c) (fun h0 => by
        rw [h0] at h1; exact h1.2 (by rw [inv_zero]; exact zero_mem _))).mp h1
      have h2' := (isInMax_iff k F w (f := f - algebraMap k F c') (fun h0 => by
        rw [h0] at h2; exact h2.2 (by rw [inv_zero]; exact zero_mem _))).mp h2
      rw [hdiff]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1' h2')
    exact (isInMax_iff k F w hu).mpr hlt |>.2 hinv
  exact ⟨hconst h.1 h'.1, hconst h.2 h'.2⟩
theorem eq_of_isCentred_of_isCentred {w w' : AlgebraicCurve.Place k F} {a b : k}
    (hab : b ^ 2 + b = a ^ 5) (h : IsCentred k F w a b) (h' : IsCentred k F w' a b) :
    w = w' := by
  have hfin : ∀ {w : AlgebraicCurve.Place k F}, IsCentred k F w a b →
      ∃ v, fltToChart k F w = Sum.inl v ∧ ChartCentred k F v a b := by
    intro w hw
    rcases hc : fltToChart k F w with v | v
    · refine ⟨v, rfl, ?_⟩
      have := (isCentred_iff_chart k F w a b).mp hw
      rwa [hc] at this
    · exact absurd (XK_mem_of_isCentred k F hw)
        ((fltToChart_eq_inr_iff k F w).mpr ⟨v, hc⟩)
  obtain ⟨v, hv, hvc⟩ := hfin h
  obtain ⟨v', hv', hvc'⟩ := hfin h'
  have : fltToChart k F w = fltToChart k F w' := by
    rw [hv, hv', chartCentred_unique k F hab hvc hvc']
  simpa [fltToChart] using this
theorem exists_isCentred {a b : k} (hab : b ^ 2 + b = a ^ 5) :
    ∃ w : AlgebraicCurve.Place k F, IsCentred k F w a b := by
  obtain ⟨v, hv⟩ := exists_chartCentred k F hab
  refine ⟨WeilConjectures.Bridge.placeEquiv k F (chartToPlace k F (Sum.inl v)), ?_⟩
  rw [isCentred_iff_chart]
  simp only [fltToChart, Equiv.symm_apply_apply]
  exact hv
theorem exists_isCentred_of_XK_mem [IsAlgClosed k] (w : AlgebraicCurve.Place k F)
    (hw : XK k F ∈ w.toValuationSubring) :
    ∃ a b : k, b ^ 2 + b = a ^ 5 ∧ IsCentred k F w a b := by
  rcases hc : fltToChart k F w with v | v
  · obtain ⟨a, b, hab, hv⟩ := exists_centre_of_finite k F v
    refine ⟨a, b, hab, ?_⟩
    rw [isCentred_iff_chart, hc]
    exact hv
  · exact absurd hw ((fltToChart_eq_inr_iff k F w).mpr ⟨v, hc⟩)
end
end WeilConjectures.Bridge.Hyperelliptic
end
section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open FunctionField
open FunctionField.Chart
open Polynomial
open scoped Polynomial RatFunc WithZero
namespace WeilConjectures.Bridge.Hyperelliptic
noncomputable section
section FiniteField
variable (k : Type*) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (m : ℕ) [NeZero m]
def extEmbedding : FiniteField.Extension (ZMod p) p m →+* k :=
  letI := ZMod.algebra k p
  (IsAlgClosed.lift (R := ZMod p) (S := FiniteField.Extension (ZMod p) p m) (M := k)).toRingHom
lemma natCard_ext : Nat.card (FiniteField.Extension (ZMod p) p m) = p ^ m := by
  rw [FiniteField.natCard_extension, Nat.card_zmod]
lemma extEmbedding_pow (e : FiniteField.Extension (ZMod p) p m) :
    extEmbedding k p m e ^ (p ^ m) = extEmbedding k p m e := by
  have : Fintype (FiniteField.Extension (ZMod p) p m) := Fintype.ofFinite _
  rw [← map_pow, ← natCard_ext p m, Nat.card_eq_fintype_card, FiniteField.pow_card]
lemma mem_range_extEmbedding {c : k} (hc : c ^ (p ^ m) = c) :
    c ∈ Set.range (extEmbedding k p m) := by
  classical
  have hp1 : 1 < p ^ m := Nat.one_lt_pow (NeZero.ne m) (Fact.out : p.Prime).one_lt
  let P : k[X] := X ^ (p ^ m) - X
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
  let S := {c : k // c ^ (p ^ m) = c}
  have hinj : Function.Injective (fun s : S => (⟨s.1, by
      rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, eval_sub, eval_pow, eval_X, s.2,
        sub_self]⟩ : P.roots.toFinset)) := by
    intro s t h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa using this
  have : Finite S := Finite.of_injective _ hinj
  have hS : Nat.card S ≤ p ^ m := by
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    refine (Multiset.toFinset_card_le _).trans ((card_roots' P).trans ?_)
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hp1]
  let f : FiniteField.Extension (ZMod p) p m → S := fun e => ⟨_, extEmbedding_pow k p m e⟩
  have hf : Function.Injective f := fun e e' h =>
    (extEmbedding k p m).injective (congrArg Subtype.val h)
  have hbij := hf.bijective_of_nat_card_le (by rw [natCard_ext]; exact hS)
  obtain ⟨e, he⟩ := hbij.2 ⟨c, hc⟩
  exact ⟨e, congrArg Subtype.val he⟩
end FiniteField
variable (k : Type*) [Field k]
variable (F : Type*) [Field F] [Algebra (HypRing k) F] [IsFractionRing (HypRing k) F]
variable [Algebra k[X] F] [IsScalarTower k[X] (HypRing k) F]
  [Algebra k⟮X⟯ F] [IsScalarTower k[X] k⟮X⟯ F]
  [_root_.FunctionField k F] [Algebra.IsSeparable k⟮X⟯ F]
  [Algebra k F] [IsScalarTower k k[X] F] [NeZero (5 : k)]
abbrev Sol : Type _ := {ab : k × k // ab.2 ^ 2 + ab.2 = ab.1 ^ 5}
def placeOf : Option (Sol k) → AlgebraicCurve.Place k F
  | none => (exists_XK_notMem k F).choose
  | some ab => (exists_isCentred k F ab.2).choose
lemma placeOf_none : XK k F ∉ (placeOf k F none).toValuationSubring :=
  (exists_XK_notMem k F).choose_spec
lemma placeOf_some (ab : Sol k) : IsCentred k F (placeOf k F (some ab)) ab.1.1 ab.1.2 :=
  (exists_isCentred k F ab.2).choose_spec
lemma placeOf_bijective [IsAlgClosed k] : Function.Bijective (placeOf k F) := by
  constructor
  · rintro (_ | ab) (_ | ab') h
    · rfl
    · exact absurd (h ▸ XK_mem_of_isCentred k F (placeOf_some k F ab')) (placeOf_none k F)
    · exact absurd (h ▸ XK_mem_of_isCentred k F (placeOf_some k F ab)) (placeOf_none k F)
    · have h1 := placeOf_some k F ab
      rw [h] at h1
      obtain ⟨ha, hb⟩ := eq_of_isCentred k F h1 (placeOf_some k F ab')
      exact congrArg some (Subtype.ext (Prod.ext ha hb))
  · intro w
    by_cases hw : XK k F ∈ w.toValuationSubring
    · obtain ⟨a, b, hab, hc⟩ := exists_isCentred_of_XK_mem k F w hw
      exact ⟨some ⟨(a, b), hab⟩,
        eq_of_isCentred_of_isCentred k F hab (placeOf_some k F ⟨(a, b), hab⟩) hc⟩
    · exact ⟨none, eq_of_XK_notMem k F (placeOf_none k F) hw⟩
variable (p : ℕ) [Fact p.Prime] [CharP k p]
lemma frob_sol (ab : Sol k) : (ab.1.2 ^ p) ^ 2 + ab.1.2 ^ p = (ab.1.1 ^ p) ^ 5 := by
  have h : (ab.1.2 ^ 2 + ab.1.2) ^ p = (ab.1.1 ^ 5) ^ p := by rw [ab.2]
  rw [add_pow_char, ← pow_mul, ← pow_mul, mul_comm 2, mul_comm 5, pow_mul, pow_mul] at h
  exact h
def frobSol : Option (Sol k) → Option (Sol k) :=
  Option.map fun ab => ⟨(ab.1.1 ^ p, ab.1.2 ^ p), frob_sol k p ab⟩
lemma frobSol_iterate (n : ℕ) (ab : Sol k) :
    ((frobSol k p)^[n] (some ab)) =
      some ⟨(ab.1.1 ^ p ^ n, ab.1.2 ^ p ^ n), by
        have h : (ab.1.2 ^ 2 + ab.1.2) ^ p ^ n = (ab.1.1 ^ 5) ^ p ^ n := by rw [ab.2]
        rw [add_pow_char_pow, ← pow_mul, ← pow_mul, mul_comm 2, mul_comm 5, pow_mul,
          pow_mul] at h
        exact h⟩ := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    congr 1
    exact Subtype.ext (Prod.ext (by simp) (by simp))
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [frobSol, Option.map_some, Option.some.injEq]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change (ab.1.1 ^ p ^ n) ^ p = ab.1.1 ^ p ^ (n + 1)
      rw [pow_succ, pow_mul]
    · change (ab.1.2 ^ p ^ n) ^ p = ab.1.2 ^ p ^ (n + 1)
      rw [pow_succ, pow_mul]
lemma frobSol_iterate_none (n : ℕ) : (frobSol k p)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl
section Restrict
variable (φ : F →ₐ[k] F) (hφi : φ.toRingHom.IsIntegral)
lemma mem_restrictAlong (w : AlgebraicCurve.Place k F) (g : F) :
    g ∈ (AlgebraicCurve.Place.restrictAlong φ hφi w).toValuationSubring ↔
      φ g ∈ w.toValuationSubring := Iff.rfl
lemma isInMax_restrictAlong (w : AlgebraicCurve.Place k F) (g : F) :
    IsInMax k F (AlgebraicCurve.Place.restrictAlong φ hφi w) g ↔ IsInMax k F w (φ g) := by
  rw [IsInMax, IsInMax, mem_restrictAlong, mem_restrictAlong, map_inv₀]
lemma isInMax_pow (w : AlgebraicCurve.Place k F) {f : F} (hf : f ≠ 0) (h : IsInMax k F w f) :
    IsInMax k F w (f ^ p) := by
  rw [isInMax_iff k F w (pow_ne_zero p hf), map_pow]
  rw [isInMax_iff k F w hf] at h
  exact pow_lt_one₀ zero_le h (Fact.out : p.Prime).ne_zero
variable (hφx : φ (XK k F) = XK k F ^ p) (hφy : φ (yF k F) = yF k F ^ p)
include hφx hφy
lemma isCentred_restrictAlong {w : AlgebraicCurve.Place k F} {a b : k}
    (h : IsCentred k F w a b) :
    IsCentred k F (AlgebraicCurve.Place.restrictAlong φ hφi w) (a ^ p) (b ^ p) := by
  have : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  constructor
  · rw [isInMax_restrictAlong, map_sub, AlgHom.commutes, hφx, map_pow, ← sub_pow_char]
    exact isInMax_pow k F p w (XK_sub_ne_zero k F a) h.1
  · rw [isInMax_restrictAlong, map_sub, AlgHom.commutes, hφy, map_pow, ← sub_pow_char]
    exact isInMax_pow k F p w (yF_sub_ne_zero k F b) h.2
lemma XK_notMem_restrictAlong {w : AlgebraicCurve.Place k F}
    (h : XK k F ∉ w.toValuationSubring) :
    XK k F ∉ (AlgebraicCurve.Place.restrictAlong φ hφi w).toValuationSubring := by
  rw [mem_restrictAlong, hφx, mem_iff_placeValuation, map_pow, not_le]
  rw [mem_iff_placeValuation, not_le] at h
  exact one_lt_pow₀ h (Fact.out : p.Prime).ne_zero
lemma semiconj_placeOf :
    Function.Semiconj (placeOf k F) (frobSol k p)
      (AlgebraicCurve.Place.restrictAlong φ hφi) := by
  rintro (_ | ab)
  · exact eq_of_XK_notMem k F (placeOf_none k F)
      (XK_notMem_restrictAlong k F p φ hφi hφx hφy (placeOf_none k F))
  · exact eq_of_isCentred_of_isCentred k F (frob_sol k p ab)
      (placeOf_some k F _) (isCentred_restrictAlong k F p φ hφi hφx hφy (placeOf_some k F ab))
abbrev FixSol (m : ℕ) : Type _ :=
  {ab : Sol k // ab.1.1 ^ p ^ m = ab.1.1 ∧ ab.1.2 ^ p ^ m = ab.1.2}
omit hφx hφy in
lemma mem_fixedPoints_frobSol_iff (m : ℕ) (ab : Sol k) :
    some ab ∈ Function.fixedPoints (frobSol k p)^[m] ↔
      ab.1.1 ^ p ^ m = ab.1.1 ∧ ab.1.2 ^ p ^ m = ab.1.2 := by
  rw [Function.mem_fixedPoints, Function.IsFixedPt, frobSol_iterate, Option.some.injEq,
    Subtype.ext_iff, Prod.ext_iff]
omit hφx hφy in
def fixedPointsFrobSolEquiv (m : ℕ) :
    Function.fixedPoints (frobSol k p)^[m] ≃ Option (FixSol k p m) where
  toFun s := match s with
    | ⟨none, _⟩ => none
    | ⟨some ab, h⟩ => some ⟨ab, (mem_fixedPoints_frobSol_iff k p m ab).mp h⟩
  invFun t := match t with
    | none => ⟨none, frobSol_iterate_none k p m⟩
    | some ab => ⟨some ab.1, (mem_fixedPoints_frobSol_iff k p m ab.1).mpr ab.2⟩
  left_inv s := by rcases s with ⟨_ | ab, h⟩ <;> rfl
  right_inv t := by rcases t with _ | ab <;> rfl
def fixedPointsEquiv [IsAlgClosed k] (m : ℕ) :
    Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[m] ≃
      Option (FixSol k p m) := by
  let e := Equiv.ofBijective _ (placeOf_bijective k F)
  have hsc := (semiconj_placeOf k F p φ hφi hφx hφy).iterate_right m
  refine (Equiv.subtypeEquiv e.symm fun w => ?_).trans (fixedPointsFrobSolEquiv k p m)
  change _ = w ↔ _ = e.symm w
  constructor
  · intro hw
    apply e.injective
    rw [e.apply_symm_apply]
    change placeOf k F _ = w
    rw [hsc.eq, show placeOf k F (e.symm w) = w from e.apply_symm_apply w]
    exact hw
  · intro hw
    have := congrArg (placeOf k F) hw
    rw [hsc.eq, show placeOf k F (e.symm w) = w from e.apply_symm_apply w] at this
    exact this
end Restrict
def extSolEquiv [IsAlgClosed k] (m : ℕ) [NeZero m] :
    {xy : FiniteField.Extension (ZMod p) p m × FiniteField.Extension (ZMod p) p m //
      xy.2 ^ 2 + xy.2 = xy.1 ^ 5} ≃ FixSol k p m := by
  let ι := extEmbedding k p m
  refine Equiv.ofBijective (fun xy => ⟨⟨(ι xy.1.1, ι xy.1.2), by
      rw [← map_pow, ← map_add, xy.2, map_pow]⟩,
      extEmbedding_pow k p m _, extEmbedding_pow k p m _⟩) ⟨?_, ?_⟩
  · intro xy xy' h
    have h1 := congrArg (fun t : FixSol k p m => t.1.1.1) h
    have h2 := congrArg (fun t : FixSol k p m => t.1.1.2) h
    exact Subtype.ext (Prod.ext (ι.injective h1) (ι.injective h2))
  · rintro ⟨⟨⟨a, b⟩, hab⟩, ha, hb⟩
    obtain ⟨x, rfl⟩ := mem_range_extEmbedding k p m ha
    obtain ⟨y, rfl⟩ := mem_range_extEmbedding k p m hb
    refine ⟨⟨(x, y), ι.injective ?_⟩, rfl⟩
    simpa using hab
theorem natCard_fixedPoints [IsAlgClosed k] (φ : F →ₐ[k] F) (hφi : φ.toRingHom.IsIntegral)
    (hφx : φ (XK k F) = XK k F ^ p) (hφy : φ (yF k F) = yF k F ^ p) (m : ℕ) [NeZero m] :
    Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[m]) =
      Nat.card {xy : FiniteField.Extension (ZMod p) p m × FiniteField.Extension (ZMod p) p m //
        xy.2 ^ 2 + xy.2 = xy.1 ^ 5} + 1 := by
  have : Finite (FixSol k p m) := Finite.of_equiv _ (extSolEquiv k p m)
  rw [Nat.card_congr (fixedPointsEquiv k F p φ hφi hφx hφy m), Finite.card_option,
    Nat.card_congr (extSolEquiv k p m)]
end
end WeilConjectures.Bridge.Hyperelliptic
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open Polynomial FiniteField
open scoped RatFunc Polynomial.Bivariate
noncomputable section
namespace WeilConjectures.Bridge.Hyperelliptic
open FunctionField FunctionField.Chart
section Main
variable [Fact (Nat.Prime 41)]
  (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod 41) K]
  (F₀ : Type*) [Field F₀] [Algebra (HypRing (ZMod 41)) F₀] [IsFractionRing (HypRing (ZMod 41)) F₀]
  (F : Type*) [Field F] [Algebra (HypRing K) F] [IsFractionRing (HypRing K) F]
theorem isScalarTower_constants (k₁ : Type*) [Field k₁] (F₁ : Type*) [Field F₁]
    [Algebra (HypRing k₁) F₁] :
    letI := algebraPolynomial k₁ F₁
    letI := FunctionField.algebraConstants k₁ F₁
    IsScalarTower k₁ (HypRing k₁) F₁ :=
  letI := algebraPolynomial k₁ F₁
  letI := FunctionField.algebraConstants k₁ F₁
  IsScalarTower.of_algebraMap_eq fun _ => rfl
include K F₀ F in
theorem zeta_of_functionFields :
    zetaOfCounts countF41 * ((1 - PowerSeries.X) * (1 - 41 * PowerSeries.X)) =
      1 - 9 * PowerSeries.X + 71 * PowerSeries.X ^ 2 - 9 * 41 * PowerSeries.X ^ 3 +
        41 ^ 2 * PowerSeries.X ^ 4 := by
  classical
  let k := ZMod 41
  have : CharP K 41 := charP_of_injective_algebraMap (algebraMap (ZMod 41) K).injective 41
  have : NeZero (5 : K) := ⟨by
    have h := (CharP.cast_eq_zero_iff K 41 5).not.mpr (by norm_num)
    exact_mod_cast h⟩
  letI : Algebra k[X] F₀ := algebraPolynomial k F₀
  haveI : IsScalarTower k[X] (HypRing k) F₀ := algebraPolynomial_isScalarTower k F₀
  letI : Algebra k⟮X⟯ F₀ := algebraRatFunc k F₀
  haveI : IsScalarTower k[X] k⟮X⟯ F₀ := algebraRatFunc_isScalarTower k F₀
  haveI : _root_.FunctionField k F₀ := functionField k F₀
  haveI : Algebra.IsSeparable k⟮X⟯ F₀ := isSeparable k F₀
  letI : Algebra k F₀ := FunctionField.algebraConstants k F₀
  haveI : IsScalarTower k k[X] F₀ := FunctionField.algebraConstants_isScalarTower k F₀
  haveI : IsScalarTower k (HypRing k) F₀ := isScalarTower_constants k F₀
  haveI : AlgebraicCurve.IsCurveOver k F₀ := WeilConjectures.Bridge.isCurveOver k F₀
  haveI : Algebra.EssFiniteType k F₀ := WeilConjectures.Bridge.essFiniteType k F₀
  letI : Algebra K[X] F := algebraPolynomial K F
  haveI : IsScalarTower K[X] (HypRing K) F := algebraPolynomial_isScalarTower K F
  letI : Algebra K⟮X⟯ F := algebraRatFunc K F
  haveI : IsScalarTower K[X] K⟮X⟯ F := algebraRatFunc_isScalarTower K F
  haveI : _root_.FunctionField K F := functionField K F
  haveI : Algebra.IsSeparable K⟮X⟯ F := isSeparable K F
  letI : Algebra K F := FunctionField.algebraConstants K F
  haveI : IsScalarTower K K[X] F := FunctionField.algebraConstants_isScalarTower K F
  haveI : IsScalarTower K (HypRing K) F := isScalarTower_constants K F
  haveI : IsFullConstantField K F := FunctionField.isFullConstantField_of_isAlgClosed K F
  haveI : AlgebraicCurve.IsCurveOver K F := WeilConjectures.Bridge.isCurveOver K F
  have hgK : AlgebraicCurve.genusFF K F = 2 := genusFF_eq_two K F
  have hQ : hypPoly K = (hypPoly k).map (mapRingHom (algebraMap k K)) :=
    (hypPoly_map k (algebraMap k K)).symm
  have hmon : (hypPoly K).Monic := hypPoly_monic K
  have hdeg : 0 < (hypPoly K).natDegree := by rw [hypPoly_natDegree]; norm_num
  have hinj : Function.Injective
      ((algebraMap (HypRing K) F).comp (adjoinRootBaseChange (hypPoly k) (hypPoly K) hQ)) :=
    fun a b h => adjoinRootBaseChange_injective (hypPoly k) (hypPoly K) hQ (hypPoly_monic k)
      (IsFractionRing.injective (HypRing K) F h)
  letI : Algebra F₀ F := (IsFractionRing.lift hinj).toAlgebra
  have hcompat : ∀ r, algebraMap F₀ F (algebraMap (HypRing k) F₀ r) =
      algebraMap (HypRing K) F (adjoinRootBaseChange (hypPoly k) (hypPoly K) hQ r) :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  obtain ⟨φ, hφdef⟩ : ∃ φ, φ = frobFractionField (hypPoly k) (hypPoly K) hQ F hmon hdeg :=
    ⟨_, rfl⟩
  have hφi : φ.toRingHom.IsIntegral :=
    hφdef ▸ frobFractionField_isIntegral (hypPoly k) (hypPoly K) hQ hmon hdeg
  have hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k) :=
    hφdef ▸ frobFractionField_apply_algebraMap (hypPoly k) (hypPoly K) hQ F₀ hmon hdeg hcompat
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ :=
    adjoin_range_algebraMap_eq_top (hypPoly k) (hypPoly K) hQ F₀ hcompat
  have hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤ :=
    exists_finset_adjoin_eq_top (hypPoly k) F₀
  have hcard : Fintype.card k = 41 := ZMod.card 41
  have hφx : φ (XK K F) = XK K F ^ 41 := by
    rw [← xF_eq_XK, hφdef, frobFractionField_algebraMap, ← map_pow]
    congr 1
    rw [xR, AdjoinRoot.algebraMap_eq, frobAdjoinRoot_of, expand_X, map_pow, hcard]
  have hφy : φ (yF K F) = yF K F ^ 41 := by
    rw [hφdef, yF, frobFractionField_algebraMap, ← map_pow]
    congr 1
    rw [yR, frobAdjoinRoot_root, hcard]
  have hN : ∀ m, 0 < m → countF41 m = placeCount k F₀ m := by
    intro m hm
    haveI : NeZero m := ⟨hm.ne'⟩
    rw [countF41, dif_neg hm.ne', ← natCard_fixedPoints K F 41 φ hφi hφx hφy m,
      (AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
        k K F₀ F hfg hgen φ hφi hφ m hm).2]
  obtain ⟨-, L, hLdeg, hL0, hLsymm, hrat, -, -⟩ :=
    lPolynomial_of_functionField k K F₀ F hfg hgen φ hφi hφ hN
  have hq : Nat.card k = 41 := Nat.card_zmod 41
  rw [hgK] at hLdeg hLsymm
  rw [hq] at hLsymm hrat
  exact zeta_eq_of_lPolynomial L hLdeg hL0 hLsymm hrat
end Main
theorem hyperelliptic_F41_zeta_proof [Fact (Nat.Prime 41)] :
    zetaOfCounts (fun m => if h : m = 0 then 0 else
        haveI : NeZero m := ⟨h⟩
        Nat.card {xy : FiniteField.Extension (ZMod 41) 41 m × FiniteField.Extension (ZMod 41) 41 m //
          xy.2 ^ 2 + xy.2 = xy.1 ^ 5} + 1) *
      ((1 - PowerSeries.X) * (1 - 41 * PowerSeries.X)) =
    1 - 9 * PowerSeries.X + 71 * PowerSeries.X ^ 2 - 9 * 41 * PowerSeries.X ^ 3 +
      41 ^ 2 * PowerSeries.X ^ 4 :=
  zeta_of_functionFields (AlgebraicClosure (ZMod 41)) (FractionRing (HypRing (ZMod 41)))
    (FractionRing (HypRing (AlgebraicClosure (ZMod 41))))
end WeilConjectures.Bridge.Hyperelliptic
end
end
open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures
theorem solution [Fact (Nat.Prime 41)] :
    zetaOfCounts (fun m => if h : m = 0 then 0 else
        haveI : NeZero m := ⟨h⟩
        Nat.card {xy : FiniteField.Extension (ZMod 41) 41 m × FiniteField.Extension (ZMod 41) 41 m //
          xy.2 ^ 2 + xy.2 = xy.1 ^ 5} + 1) *
      ((1 - PowerSeries.X) * (1 - 41 * PowerSeries.X)) =
    1 - 9 * PowerSeries.X + 71 * PowerSeries.X ^ 2 - 9 * 41 * PowerSeries.X ^ 3 +
      41 ^ 2 * PowerSeries.X ^ 4 :=
  WeilConjectures.Bridge.Hyperelliptic.hyperelliptic_F41_zeta_proof
