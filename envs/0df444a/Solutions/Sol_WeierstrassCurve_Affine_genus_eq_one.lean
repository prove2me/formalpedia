-- Prove2me | solution 1 for WeierstrassCurve.Affine.genus_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T15:08:28.603692+00:00
-- url     : https://prove2.me/submissions/c31ef74c-9d58-4915-aa5b-371410a0c67f

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassGenus
import Theorems.Thm_FunctionField_Chart_placeValuation_algebraMap_eq_one
import Theorems.Thm_FunctionField_genus_eq_genusChart
import Theorems.Thm_WeierstrassCurve_Affine_Chart_infinity_ramificationIdx_eq_two
import Theorems.Thm_WeierstrassCurve_Affine_Chart_infinity_heightOne_unique
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
include W in
theorem finrank_ratFunc_eq_two : Module.finrank k⟮X⟯ K = 2 := by
  rw [Module.finrank_eq_card_basis (W.basisRatFunc K), Fintype.card_fin]
end AbstractRatFuncAlgebra
end AbstractPolynomialAlgebra
end WeierstrassCurve.Affine
namespace FunctionField
open scoped Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k[X] K]
end FunctionField
end
end
end
section
section
open FunctionField
open FunctionField.Chart
open Polynomial
open scoped Polynomial RatFunc
namespace WeierstrassCurve.Affine.Chart
noncomputable section
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K]
  [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] WeierstrassCurve.Affine.Chart.instAlgebraConstants
attribute [local instance] WeierstrassCurve.Affine.Chart.instConstantsTower
attribute [local instance] WeierstrassCurve.Affine.Chart.instCoordinateConstantsTower
local notation "A∞" => inftyValuationSubring k
local notation "S∞" => infiniteIntegers k K
attribute [local instance] WeierstrassCurve.Affine.Chart.instFaithfulInfinity
attribute [local instance] WeierstrassCurve.Affine.Chart.instInfinityConstantsTower
include W in
omit [WeierstrassCurve.IsElliptic W] in
lemma infinity_sum_ramification_inertia :
    let p := IsLocalRing.maximalIdeal A∞
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S∞,
      p.ramificationIdx' P * p.inertiaDeg' P = 2 := by
  dsimp
  have hp0 : IsLocalRing.maximalIdeal A∞ ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  rw [Ideal.sum_ramification_inertia S∞ k⟮X⟯ K hp0,
    W.finrank_ratFunc_eq_two K]
include W in
omit [WeierstrassCurve.IsElliptic W] in
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
  letI : P.LiesOver p := ⟨hunder.symm⟩
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := P)).2
      ⟨v.isPrime, (show P.LiesOver p from inferInstance)⟩
  let g : Ideal S∞ → ℕ := fun Q => p.ramificationIdx' Q * p.inertiaDeg' Q
  have hsum : (∑ Q ∈ IsDedekindDomain.primesOverFinset p S∞, g Q) = 2 := by
    simpa [g] using infinity_sum_ramification_inertia W K
  have hterm : g P ≤ 2 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ hP]
    omega
  have he : p.ramificationIdx' P = 2 := infinity_ramificationIdx_eq_two W K v
  have hfpos : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
  dsimp [g] at hterm
  rw [he] at hterm
  change p.inertiaDeg' P = 1
  omega
include W in
omit [WeierstrassCurve.IsElliptic W] in
theorem infinityPlace_deg_one : placeDegree k K (infinityPlace K) = 1 := by
  rw [infinityPlace, placeDegree_infinite_eq_inertiaDeg]
  have hunder : (infinityHeightOne (k := k) K).asIdeal.under A∞ =
      IsLocalRing.maximalIdeal A∞ :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.under A∞ (infinityHeightOne (k := k) K).asIdeal)
  rw [hunder]
  exact infinity_inertiaDeg_eq_one W K (infinityHeightOne (k := k) K)
end
end WeierstrassCurve.Affine.Chart
end
end
section
section
open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc WithZero
namespace WeierstrassCurve.Affine.Chart
noncomputable section
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]
local instance instCoordinateConstantsTowerGenus : IsScalarTower k W.CoordinateRing K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing,
      ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]
omit [WeierstrassCurve.IsElliptic W] [IsFullConstantField k K] in
lemma yCoord_order_at_infinity :
    principalDivisorA k K
      (Additive.ofMul (Units.mk0 (W.yCoord K) (yCoord_ne_zero W K)))
      (infinityPlace K) = -3 := by
  let w := infinityHeightOne (k := k) K
  let V := placeValuation k K (Sum.inr w)
  let y := W.yCoord K
  let x := XK k K
  let n := principalDivisorA k K
    (Additive.ofMul (Units.mk0 y (yCoord_ne_zero W K))) (Sum.inr w)
  have hvy : V y = WithZero.exp (-n) :=
    placeValuation_eq_exp_neg_principalDivisor k K
      (Additive.ofMul (Units.mk0 y (yCoord_ne_zero W K))) (Sum.inr w)
  have hvx : V x = WithZero.exp (2 : ℤ) := by
    have h := placeValuation_eq_exp_neg_principalDivisor k K
      (Additive.ofMul (Units.mk0 x (XK_ne_zero k K))) (Sum.inr w)
    rw [principalDivisorA_XK_at_infinite k K w] at h
    have he : ramIdxInfty k K w.asIdeal = 2 := infinity_ramificationIdx_eq_two W K w
    rw [he] at h
    simpa [V, x] using h
  have hconst (a : k) : V (algebraMap k K a) ≤ 1 :=
    placeValuation_algebraMap_le_one k K (Sum.inr w) a
  have hEq :
      y ^ 2 + algebraMap k K W.a₁ * x * y + algebraMap k K W.a₃ * y =
        x ^ 3 + algebraMap k K W.a₂ * x ^ 2 + algebraMap k K W.a₄ * x +
          algebraMap k K W.a₆ := by
    have h := (coordinate_equation W).map (algebraMap W.CoordinateRing K)
    have hx : algebraMap W.CoordinateRing K
        (CoordinateRing.mk W (Polynomial.C Polynomial.X)) = x := by
      exact xCoord_eq_XK W K
    have hy : algebraMap W.CoordinateRing K (CoordinateRing.mk W Polynomial.X) = y := rfl
    have hc (a : k) : algebraMap W.CoordinateRing K (algebraMap k W.CoordinateRing a) =
        algebraMap k K a := (IsScalarTower.algebraMap_apply k W.CoordinateRing K a).symm
    apply (W⁄K).equation_iff x y |>.mp
    convert h using 1
    · ext <;> simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map]
      all_goals exact (hc _).symm
    · exact hx.symm
    · exact hy.symm
  have hRHS : V (x ^ 3 + algebraMap k K W.a₂ * x ^ 2 +
      algebraMap k K W.a₄ * x + algebraMap k K W.a₆) = WithZero.exp (6 : ℤ) := by
    have hx3 : V (x ^ 3) = WithZero.exp (6 : ℤ) := by
      rw [map_pow, hvx, ← WithZero.exp_nsmul]
      norm_num
    have ha2 : V (algebraMap k K W.a₂ * x ^ 2) < WithZero.exp (6 : ℤ) := by
      rw [map_mul, map_pow, hvx, ← WithZero.exp_nsmul]
      refine lt_of_le_of_lt (mul_le_mul (hconst W.a₂) le_rfl zero_le zero_le) ?_
      rw [one_mul]
      convert WithZero.exp_lt_exp.mpr (show (4 : ℤ) < 6 by omega) using 1; norm_num
    have h1 : V (x ^ 3 + algebraMap k K W.a₂ * x ^ 2) = WithZero.exp (6 : ℤ) := by
      rw [V.map_add_eq_of_lt_left (by rw [hx3]; exact ha2), hx3]
    have ha4 : V (algebraMap k K W.a₄ * x) < WithZero.exp (6 : ℤ) := by
      rw [map_mul, hvx]
      refine lt_of_le_of_lt (mul_le_mul (hconst W.a₄) le_rfl zero_le zero_le) ?_
      simpa only [one_mul] using WithZero.exp_lt_exp.mpr (show (2 : ℤ) < 6 by omega)
    have h2 : V (x ^ 3 + algebraMap k K W.a₂ * x ^ 2 + algebraMap k K W.a₄ * x) =
        WithZero.exp (6 : ℤ) := by
      rw [V.map_add_eq_of_lt_left (h1 ▸ ha4), h1]
    have ha6 : V (algebraMap k K W.a₆) < WithZero.exp (6 : ℤ) := by
      exact lt_of_le_of_lt (hconst W.a₆)
        (by simpa only [WithZero.exp_zero] using
          WithZero.exp_lt_exp.mpr (show (0 : ℤ) < 6 by omega))
    rw [V.map_add_eq_of_lt_left (h2 ▸ ha6), h2]
  have hnlt : n < -2 := by
    by_contra hn
    have hn' : -2 ≤ n := le_of_not_gt hn
    have hy_le : V y ≤ WithZero.exp (2 : ℤ) := by
      rw [hvy]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hLHSle : V (y ^ 2 + algebraMap k K W.a₁ * x * y +
        algebraMap k K W.a₃ * y) ≤ WithZero.exp (4 : ℤ) := by
      refine (V.map_add _ _).trans (max_le ?_ ?_)
      · refine (V.map_add _ _).trans (max_le ?_ ?_)
        · rw [map_pow]
          exact (pow_le_pow_left' hy_le 2).trans_eq (by rw [← WithZero.exp_nsmul]; norm_num)
        · rw [map_mul, map_mul, hvx]
          calc
            V (algebraMap k K W.a₁) * WithZero.exp 2 * V y
                ≤ 1 * WithZero.exp 2 * WithZero.exp 2 := by
                  gcongr
                  exact hconst W.a₁
            _ = WithZero.exp 4 := by rw [one_mul, ← WithZero.exp_add]; norm_num
      · rw [map_mul]
        calc
          V (algebraMap k K W.a₃) * V y ≤ 1 * WithZero.exp 2 := by
            gcongr
            exact hconst W.a₃
          _ ≤ WithZero.exp 4 := by
            rw [one_mul]
            exact WithZero.exp_le_exp.mpr (by omega)
    rw [hEq, hRHS] at hLHSle
    exact (not_le_of_gt (WithZero.exp_lt_exp.mpr (show (4 : ℤ) < 6 by omega))) hLHSle
  have hnle : n ≤ -3 := by omega
  by_cases hn3 : n = -3
  · simpa [infinityPlace, n, w] using hn3
  have hn4 : n ≤ -4 := by omega
  have hy2 : V (y ^ 2) = WithZero.exp (-2 * n) := by
    rw [map_pow, hvy, ← WithZero.exp_nsmul]
    congr 1
    ring
  have hrest : V (algebraMap k K W.a₁ * x * y + algebraMap k K W.a₃ * y) <
      WithZero.exp (-2 * n) := by
    refine lt_of_le_of_lt (V.map_add _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_mul, hvx, hvy]
      calc
        V (algebraMap k K W.a₁) * WithZero.exp 2 * WithZero.exp (-n)
            ≤ 1 * WithZero.exp 2 * WithZero.exp (-n) := by
              gcongr
              exact hconst W.a₁
        _ = WithZero.exp (2 - n) := by rw [one_mul, ← WithZero.exp_add]; congr 1
        _ < WithZero.exp (-2 * n) := WithZero.exp_lt_exp.mpr (by omega)
    · rw [map_mul, hvy]
      calc
        V (algebraMap k K W.a₃) * WithZero.exp (-n) ≤ 1 * WithZero.exp (-n) := by
          gcongr
          exact hconst W.a₃
        _ = WithZero.exp (-n) := one_mul _
        _ < WithZero.exp (-2 * n) := WithZero.exp_lt_exp.mpr (by omega)
  have hLHS : V (y ^ 2 + (algebraMap k K W.a₁ * x * y + algebraMap k K W.a₃ * y)) =
      WithZero.exp (-2 * n) := by
    rw [V.map_add_eq_of_lt_left (by rw [hy2]; exact hrest), hy2]
  have hexp : WithZero.exp (-2 * n) = WithZero.exp (6 : ℤ) := by
    calc
      WithZero.exp (-2 * n) = V (y ^ 2 +
          (algebraMap k K W.a₁ * x * y + algebraMap k K W.a₃ * y)) := hLHS.symm
      _ = V (x ^ 3 + algebraMap k K W.a₂ * x ^ 2 +
          algebraMap k K W.a₄ * x + algebraMap k K W.a₆) := by
            apply congrArg V
            rw [← add_assoc]
            exact hEq
      _ = WithZero.exp 6 := hRHS
  have : -2 * n = 6 := WithZero.exp_injective hexp
  omega
include W in
omit [WeierstrassCurve.IsElliptic W] [Algebra k K] [IsScalarTower k k[X] K]
  [IsFullConstantField k K] in
lemma deg_infinityDivisor : deg k K (infinityDivisor (k := k) K) = 1 := by
  rw [infinityDivisor, deg_single, infinityPlace_deg_one W K]
  norm_num
include W in
omit [WeierstrassCurve.IsElliptic W] [IsFullConstantField k K] in
lemma polarDivisor_XK_eq_two_infinity :
    polarDivisor k K (XK k K) = 2 • infinityDivisor (k := k) K := by
  classical
  ext v
  rcases v with v | v
  · rw [polarDivisor_XK_zero_at_finite]
    have hne : infinityPlace K ≠ Sum.inl v := by intro h; cases h
    simp [infinityDivisor, hne]
  · have hv : v = infinityHeightOne (k := k) K := infinity_heightOne_unique W K _ _
    subst v
    rw [polarDivisor_XK_at_infinite]
    have he : ramIdxInfty k K (infinityHeightOne (k := k) K).asIdeal = 2 :=
      infinity_ramificationIdx_eq_two W K _
    rw [he]
    simp [infinityDivisor, infinityPlace]
omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma yCoord_mem_ringOfIntegers :
    ∃ a : ringOfIntegers k K, (a : K) = W.yCoord K := by
  let yR : W.CoordinateRing := CoordinateRing.mk W Polynomial.X
  have hyintR : _root_.IsIntegral k[X] yR := Algebra.IsIntegral.isIntegral yR
  have hyintK : _root_.IsIntegral k[X] (W.yCoord K) := by
    simpa [yCoord, yR] using hyintR.map (IsScalarTower.toAlgHom k[X] W.CoordinateRing K)
  exact ⟨⟨W.yCoord K, hyintK⟩, rfl⟩
include W in
omit [WeierstrassCurve.IsElliptic W] [Algebra k K] [IsScalarTower k k[X] K]
  [IsFullConstantField k K] in
lemma polarDivisor_yCoord_zero_at_finite
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    polarDivisor k K (W.yCoord K) (Sum.inl v) = 0 := by
  have hy0 := yCoord_ne_zero W K
  obtain ⟨a, ha⟩ := yCoord_mem_ringOfIntegers W K
  have ha0 : a ≠ 0 := fun ha0 => hy0 (by simpa [ha] using congrArg Subtype.val ha0)
  have hprincipal :
      0 ≤ principalDivisorA k K
        (Additive.ofMul (Units.mk0 (W.yCoord K) hy0)) (Sum.inl v) := by
    simpa [ha] using
      principalDivisorA_nonneg_at_finite_of_mem_ringOfIntegers (k := k) (K := K) ha0 v
  unfold polarDivisor
  simp only [dif_neg hy0, Finsupp.sup_apply]
  exact max_eq_right (neg_nonpos.mpr hprincipal)
include W in
omit [WeierstrassCurve.IsElliptic W] [IsFullConstantField k K] in
lemma polarDivisor_yCoord_eq_three_infinity :
    polarDivisor k K (W.yCoord K) = 3 • infinityDivisor (k := k) K := by
  classical
  ext v
  rcases v with v | v
  · rw [polarDivisor_yCoord_zero_at_finite]
    have hne : infinityPlace K ≠ Sum.inl v := by intro h; cases h
    simp [infinityDivisor, hne]
  · have hv : v = infinityHeightOne (k := k) K := infinity_heightOne_unique W K _ _
    subst v
    have hy0 := yCoord_ne_zero W K
    have hord := yCoord_order_at_infinity W K
    have hord' : principalDivisorA k K
        (Additive.ofMul (Units.mk0 (W.yCoord K) hy0)) (infinityPlace K) = -3 := by
      simpa only using hord
    change polarDivisor k K (W.yCoord K) (infinityPlace K) = _
    unfold polarDivisor
    rw [dif_neg hy0]
    change max (-principalDivisorA k K
      (Additive.ofMul (Units.mk0 (W.yCoord K) hy0)) (infinityPlace K)) 0 = _
    rw [hord']
    simp [infinityDivisor, infinityPlace]
include W in
omit [WeierstrassCurve.IsElliptic W] [IsFullConstantField k K] in
lemma valuation_aeval_XK (p : k[X]) (hp : p ≠ 0) :
    placeValuation k K (infinityPlace K) (Polynomial.aeval (XK k K) p) =
      WithZero.exp (2 * p.natDegree : ℤ) := by
  let V := placeValuation k K (infinityPlace K)
  letI : V.IsTrivialOn k :=
    ⟨fun a ha => by
      simpa [V] using placeValuation_algebraMap_eq_one k K (infinityPlace K) (Units.mk0 a ha)⟩
  have hvx : V (XK k K) = WithZero.exp (2 : ℤ) := by
    have h := placeValuation_eq_exp_neg_principalDivisor k K
      (Additive.ofMul (Units.mk0 (XK k K) (XK_ne_zero k K)))
      (infinityPlace K)
    rw [show infinityPlace K = Sum.inr (infinityHeightOne (k := k) K) from rfl,
      principalDivisorA_XK_at_infinite,
      show ramIdxInfty k K (infinityHeightOne (k := k) K).asIdeal = 2 by
        exact infinity_ramificationIdx_eq_two W K _] at h
    change placeValuation k K (Sum.inr (infinityHeightOne (k := k) K)) (XK k K) =
      WithZero.exp (-(-((2 : ℕ) : ℤ))) at h
    norm_num at h
    simpa only [V, infinityPlace] using h
  rw [Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
    (XK k K) (by rw [hvx, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by omega)) hp,
    hvx, ← WithZero.exp_nsmul]
  congr 1
  ring
include W in
omit [WeierstrassCurve.IsElliptic W] [IsFullConstantField k K] in
lemma valuation_aeval_XK_mul_yCoord (q : k[X]) (hq : q ≠ 0) :
    placeValuation k K (infinityPlace K)
      (Polynomial.aeval (XK k K) q * W.yCoord K) =
        WithZero.exp (2 * q.natDegree + 3 : ℤ) := by
  rw [map_mul, valuation_aeval_XK W K q hq]
  have hy := placeValuation_eq_exp_neg_principalDivisor k K
    (Additive.ofMul (Units.mk0 (W.yCoord K) (yCoord_ne_zero W K))) (infinityPlace K)
  rw [yCoord_order_at_infinity W K] at hy
  have hy' : placeValuation k K (infinityPlace K) (W.yCoord K) = WithZero.exp (3 : ℤ) := by
    change placeValuation k K (infinityPlace K) (W.yCoord K) = WithZero.exp (-(-3 : ℤ)) at hy
    norm_num at hy
    exact hy
  rw [hy', ← WithZero.exp_add]
include W in
omit [IsFullConstantField k K] in
lemma ell_infinity_eq_one : ell k K (infinityDivisor (k := k) K) = 1 := by
  let D := infinityDivisor (k := k) K
  let φ : k →ₗ[k] RRspace k K D :=
    { toFun := fun c => ⟨algebraMap k K c, by
        intro v
        have hc := placeValuation_algebraMap_le_one k K v c
        rcases v with v | v
        · simpa [D, infinityDivisor, Finsupp.single_apply, infinityPlace] using hc
        · have hv : v = infinityHeightOne (k := k) K := infinity_heightOne_unique W K _ _
          subst v
          exact hc.trans (WithZero.exp_le_exp.mpr (by simp [D, infinityDivisor, infinityPlace])) ⟩
      map_add' := fun x y => Subtype.ext (map_add (algebraMap k K) x y)
      map_smul' := fun c x => Subtype.ext (by simp [Algebra.smul_def]) }
  have hφ : Function.Bijective φ := by
    constructor
    · intro c d hcd
      apply (algebraMap k K).injective
      exact congrArg Subtype.val hcd
    · intro f
      have hfin := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
        (R := ringOfIntegers k K) K (f : K) (fun v => by
          have hv := f.property (Sum.inl v)
          have hne : infinityPlace K ≠ Sum.inl v := by intro h; cases h
          have hv' : placeValuation k K (Sum.inl v) (f : K) ≤ 1 := by
            simpa [D, infinityDivisor, Finsupp.single_apply, hne] using hv
          exact hv')
      obtain ⟨a, ha⟩ := hfin
      let e := coordinateRingEquivIntegers W K
      let r : W.CoordinateRing := e.symm a
      have hrK : algebraMap W.CoordinateRing K r = (f : K) := by
        have hemb := IsIntegralClosure.algebraMap_equiv k[X] W.CoordinateRing K
          (ringOfIntegers k K) r
        change algebraMap (ringOfIntegers k K) K ((coordinateRingEquivIntegers W K) r) =
          algebraMap W.CoordinateRing K r at hemb
        calc
          algebraMap W.CoordinateRing K r = algebraMap (ringOfIntegers k K) K (e r) := by
            exact hemb.symm
          _ = (a : K) := by rw [e.apply_symm_apply]; rfl
          _ = (f : K) := ha
      obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq r
      have hfdecomp : Polynomial.aeval (XK k K) p +
          Polynomial.aeval (XK k K) q * W.yCoord K = (f : K) := by
        calc
          Polynomial.aeval (XK k K) p + Polynomial.aeval (XK k K) q * W.yCoord K =
              algebraMap k[X] K p + algebraMap k[X] K q * W.yCoord K := by
                rw [algebraMap_polynomial_eq_aeval_XK, algebraMap_polynomial_eq_aeval_XK]
          _ = algebraMap W.CoordinateRing K
              (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W Polynomial.X) := by
                simp [Algebra.smul_def, IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K,
                  yCoord]
          _ = algebraMap W.CoordinateRing K r := congrArg _ hpq
          _ = (f : K) := hrK
      have hvinf := f.property (infinityPlace K)
      have hDinf : D (infinityPlace K) = 1 := by
        simp [D, infinityDivisor]
      rw [hDinf] at hvinf
      by_cases hq : q = 0
      · subst q
        simp only [map_zero, zero_mul, add_zero] at hfdecomp
        by_cases hp : p = 0
        · subst p
          refine ⟨0, Subtype.ext ?_⟩
          dsimp [φ]
          simpa using hfdecomp
        · have hpval := valuation_aeval_XK W K p hp
          have hvp_le : WithZero.exp (2 * p.natDegree : ℤ) ≤ WithZero.exp (1 : ℤ) := by
            rw [← hpval, hfdecomp]
            exact hvinf
          have hpdeg : p.natDegree = 0 := by
            have := WithZero.exp_le_exp.mp hvp_le
            omega
          refine ⟨p.coeff 0, Subtype.ext ?_⟩
          change algebraMap k K (p.coeff 0) = (f : K)
          rw [← hfdecomp, Polynomial.eq_C_of_natDegree_eq_zero hpdeg]
          simp
      · have hqval := valuation_aeval_XK_mul_yCoord W K q hq
        by_cases hp : p = 0
        · subst p
          simp only [map_zero, zero_add] at hfdecomp
          have hbad : WithZero.exp (3 : ℤ) ≤ WithZero.exp (1 : ℤ) := by
            refine (WithZero.exp_le_exp.mpr
              (show (3 : ℤ) ≤ 2 * q.natDegree + 3 by omega)).trans ?_
            rw [← hqval, hfdecomp]
            exact hvinf
          exact ((not_le_of_gt (WithZero.exp_lt_exp.mpr
            (show (1 : ℤ) < 3 by omega))) hbad).elim
        · have hpval := valuation_aeval_XK W K p hp
          have hne : (2 * p.natDegree : ℤ) ≠ 2 * q.natDegree + 3 := by omega
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hsum : placeValuation k K (infinityPlace K)
                (Polynomial.aeval (XK k K) p +
                Polynomial.aeval (XK k K) q * W.yCoord K) =
                WithZero.exp (2 * q.natDegree + 3 : ℤ) := by
              rw [(placeValuation k K (infinityPlace K)).map_add_eq_of_lt_right (by
                rw [hpval, hqval]
                exact WithZero.exp_lt_exp.mpr hlt), hqval]
            have hbad : WithZero.exp (3 : ℤ) ≤ WithZero.exp (1 : ℤ) := by
              refine (WithZero.exp_le_exp.mpr
                (show (3 : ℤ) ≤ 2 * q.natDegree + 3 by omega)).trans ?_
              rw [← hsum, hfdecomp]
              exact hvinf
            exact ((not_le_of_gt (WithZero.exp_lt_exp.mpr
              (show (1 : ℤ) < 3 by omega))) hbad).elim
          · have hsum : placeValuation k K (infinityPlace K)
                (Polynomial.aeval (XK k K) p +
                Polynomial.aeval (XK k K) q * W.yCoord K) =
                WithZero.exp (2 * p.natDegree : ℤ) := by
              rw [(placeValuation k K (infinityPlace K)).map_add_eq_of_lt_left (by
                rw [hpval, hqval]
                exact WithZero.exp_lt_exp.mpr hgt), hpval]
            have hbad : WithZero.exp (2 : ℤ) ≤ WithZero.exp (1 : ℤ) := by
              refine (WithZero.exp_le_exp.mpr
                (show (2 : ℤ) ≤ 2 * p.natDegree by omega)).trans ?_
              rw [← hsum, hfdecomp]
              exact hvinf
            exact ((not_le_of_gt (WithZero.exp_lt_exp.mpr
              (show (1 : ℤ) < 2 by omega))) hbad).elim
  let e : k ≃ₗ[k] RRspace k K D := LinearEquiv.ofBijective φ hφ
  change Module.finrank k (RRspace k K D) = 1
  rw [← e.finrank_eq]
  exact Module.finrank_self k
include W in
omit [WeierstrassCurve.IsElliptic W] [IsFullConstantField k K] in
lemma ell_nsmul_infinity_ge_add (r a b : ℕ)
    (ha : ∀ j : Fin a, 2 * (j : ℕ) ≤ r)
    (hb : ∀ j : Fin b, 2 * (j : ℕ) + 3 ≤ r) :
    a + b ≤ ell k K (r • infinityDivisor (k := k) K) := by
  classical
  have hDnn : 0 ≤ infinityDivisor (k := k) K := by
    intro v
    rw [infinityDivisor, Finsupp.single_apply]
    split <;> simp
  let basis := W.basisRatFunc K
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
  let f : Fin a ⊕ Fin b → K := fun i =>
    basis (g i).1 * (XK k K) ^ ((g i).2 : ℕ)
  have hlin : LinearIndependent k f := by
    exact (linearIndependent_basis_smul_XK_pow (k := k) (K := K) basis).comp g hg
  have hmem : ∀ i, f i ∈ RRspace k K (r • infinityDivisor (k := k) K) := by
    intro i
    rw [mem_RRspace_iff]
    rcases i with j | j
    · have hx := memRRspace_smul_polar (k := k) (K := K) (XK_ne_zero k K) (j : ℕ)
      have hx' : memRRspace k K (((j : ℕ) * 2) • infinityDivisor (k := k) K)
          ((XK k K) ^ (j : ℕ)) := by
        convert hx using 1
        ext v
        rw [polarDivisor_XK_eq_two_infinity W K]
        simp only [Finsupp.nsmul_apply]
        ring
      have hle : ((j : ℕ) * 2) • infinityDivisor (k := k) K ≤
          r • infinityDivisor (k := k) K := by
        intro v
        simp only [Finsupp.nsmul_apply]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simpa [mul_comm] using ha j))
          (hDnn v)
      simpa [f, g, basis] using
        (memRRspace.memRRspace_mono (k := k) (K := K) hle hx')
    · have hx := memRRspace_smul_polar (k := k) (K := K) (XK_ne_zero k K) (j : ℕ)
      have hy := memRRspace_polarDivisor_of_ne_zero (k := k) (K := K) (yCoord_ne_zero W K)
      have hmul := memRRspace.mul_mem (k := k) (K := K) hx hy
      have hxy : memRRspace k K (((j : ℕ) * 2 + 3) • infinityDivisor (k := k) K)
          ((XK k K) ^ (j : ℕ) * W.yCoord K) := by
        convert hmul using 1
        ext v
        rw [polarDivisor_XK_eq_two_infinity W K,
          polarDivisor_yCoord_eq_three_infinity W K]
        simp only [Finsupp.nsmul_apply, Finsupp.add_apply]
        ring
      have hle : ((j : ℕ) * 2 + 3) • infinityDivisor (k := k) K ≤
          r • infinityDivisor (k := k) K := by
        intro v
        simp only [Finsupp.nsmul_apply]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by simpa [mul_comm] using hb j))
          (hDnn v)
      simpa [f, g, basis, mul_comm] using
        (memRRspace.memRRspace_mono (k := k) (K := K) hle hxy)
  have hspan : Submodule.span k (Set.range f) ≤
      RRspace k K (r • infinityDivisor (k := k) K) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hcard : a + b = Module.finrank k (Submodule.span k (Set.range f)) := by
    rw [finrank_span_eq_card hlin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  rw [hcard]
  exact Submodule.finrank_mono hspan
include W in
omit [WeierstrassCurve.IsElliptic W] [IsFullConstantField k K] in
lemma ell_nsmul_infinity_ge (r : ℕ) :
    r ≤ ell k K (r • infinityDivisor (k := k) K) := by
  by_cases heven : r % 2 = 0
  · let m := r / 2
    have hr : r = 2 * m := by omega
    by_cases hm : m = 0
    · have : r = 0 := by omega
      rw [this]
      exact Nat.zero_le _
    · have h := ell_nsmul_infinity_ge_add W K r (m + 1) (m - 1)
          (fun j => by have := j.isLt; omega)
          (fun j => by have := j.isLt; omega)
      omega
  · have hodd : r % 2 = 1 := by omega
    let m := r / 2
    have hr : r = 2 * m + 1 := by omega
    have h := ell_nsmul_infinity_ge_add W K r (m + 1) m
      (fun j => by have := j.isLt; omega)
      (fun j => by have := j.isLt; omega)
    omega
include W in
lemma genus_eq_one_counting : FunctionField.Chart.genus k K = 1 := by
  let B := infinityDivisor (k := k) K
  have hdegB : deg k K B = 1 := deg_infinityDivisor W K
  have hmono : ∀ r : ℕ, FunctionField.Chart.defect k K (0 + r • B) ≤ 1 := by
    intro r
    have hell : r ≤ FunctionField.Chart.ell k K (r • B) := by
      simpa [B] using ell_nsmul_infinity_ge W K r
    have hdeg : deg k K (r • B) = r := by
      rw [deg_nsmul, hdegB]
      norm_num
    dsimp only [FunctionField.Chart.defect]
    rw [zero_add, hdeg]
    exact_mod_cast (show (r : ℤ) + 1 - FunctionField.Chart.ell k K (r • B) ≤ 1 by omega)
  have hgrow : ∀ m : ℤ, ∃ r : ℕ, m ≤ FunctionField.Chart.ell k K (0 + r • B) := by
    intro m
    by_cases hm : m ≤ 0
    · exact ⟨0, by simp; omega⟩
    · let r := m.toNat
      have hr : (r : ℤ) = m := Int.toNat_of_nonneg (le_of_lt (lt_of_not_ge hm))
      refine ⟨r, ?_⟩
      rw [zero_add, ← hr]
      exact_mod_cast ell_nsmul_infinity_ge W K r
  have hall : ∀ D : DivisorA k K, FunctionField.Chart.defect k K D ≤ 1 :=
    defect_le_of_family (k := k) (K := K) B 0 1 hmono hgrow
  have hgen_le : FunctionField.Chart.genus k K ≤ 1 := by
    obtain ⟨D, hD⟩ := exists_defect_eq (k := k) (K := K)
    have h := hall D
    rw [hD] at h
    exact_mod_cast h
  have hdefB : FunctionField.Chart.defect k K B = 1 := by
    dsimp only [FunctionField.Chart.defect]
    rw [hdegB, ell_infinity_eq_one W K]
    norm_num
  have hgen_ge : 1 ≤ FunctionField.Chart.genus k K := by
    have h := defect_le k K B
    rw [hdefB] at h
    exact_mod_cast h
  omega
end
end WeierstrassCurve.Affine.Chart
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
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]
include W
theorem genus_eq_one : FunctionField.Chart.genus k K = 1 := by
  exact genus_eq_one_counting W K
end WeierstrassCurve.Affine.Chart
end
end
open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc nonZeroDivisors
open WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]
include W
namespace WeierstrassCurve.Affine
theorem _root_.solution : FunctionField.genus k K = 1 :=
  (FunctionField.genus_eq_genusChart k K).trans (Chart.genus_eq_one W K)
end WeierstrassCurve.Affine
