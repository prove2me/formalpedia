-- Prove2me | solution 1 for WeierstrassCurve.Affine.Chart.infinity_ramificationIdx_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:36:39.262469+00:00
-- url     : https://prove2.me/submissions/2d959ff6-ee7e-4917-88ac-9265e9bdbea7

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassInfinity
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
local instance instNoZeroSMulDivisorsInfinity : NoZeroSMulDivisors A∞ S∞ := ⟨by
  intro c x h
  rw [Algebra.smul_def] at h
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hc | hx
  · exact Or.inl ((faithfulSMul_iff_algebraMap_injective A∞ S∞).mp inferInstance
      (by simpa using hc))
  · exact Or.inr hx
⟩
attribute [local instance] WeierstrassCurve.Affine.Chart.instInfinityConstantsTower
omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma infinityZInt_equation :
    let z := infinityZInt W K
    let t := infinityTInt (k := k) K
    let c : k →+* S∞ := (algebraMap A∞ S∞).comp (algebraMap k A∞)
    z ^ 2 + (c W.a₁ * t + c W.a₃ * t ^ 2) * z -
      (t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4) = 0 := by
  dsimp
  apply Subtype.ext
  change (infinityZ W K) ^ 2 +
      (algebraMap A∞ K (algebraMap k A∞ W.a₁) * algebraMap A∞ K (tA k) +
        algebraMap A∞ K (algebraMap k A∞ W.a₃) * (algebraMap A∞ K (tA k)) ^ 2) *
        infinityZ W K -
    (algebraMap A∞ K (tA k) +
      algebraMap A∞ K (algebraMap k A∞ W.a₂) * (algebraMap A∞ K (tA k)) ^ 2 +
      algebraMap A∞ K (algebraMap k A∞ W.a₄) * (algebraMap A∞ K (tA k)) ^ 3 +
      algebraMap A∞ K (algebraMap k A∞ W.a₆) * (algebraMap A∞ K (tA k)) ^ 4) = 0
  have htmap : algebraMap A∞ K (tA k) = tK k K := rfl
  rw [htmap,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₁,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₃,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₂,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₄,
    ← IsScalarTower.algebraMap_apply k A∞ K W.a₆]
  exact infinityZ_equation W K
include W in
omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] in
lemma infinity_map_maximalIdeal_le_sq
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    Ideal.map (algebraMap A∞ S∞) (IsLocalRing.maximalIdeal A∞) ≤ v.asIdeal ^ 2 := by
  let P := v.asIdeal
  let z := infinityZInt W K
  let t := infinityTInt (k := k) K
  let c : k →+* S∞ := (algebraMap A∞ S∞).comp (algebraMap k A∞)
  have hunder : P.under A∞ = IsLocalRing.maximalIdeal A∞ :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  have hmap : Ideal.map (algebraMap A∞ S∞) (IsLocalRing.maximalIdeal A∞) ≤ P := by
    rw [← hunder]
    exact Ideal.map_comap_le
  have htA : tA k ∈ IsLocalRing.maximalIdeal A∞ := by
    rw [maximalIdeal_infty_eq_span_t k]
    exact Ideal.mem_span_singleton_self (tA k)
  have ht : t ∈ P := hmap (Ideal.mem_map_of_mem (algebraMap A∞ S∞) htA)
  have hBt : c W.a₁ * t + c W.a₃ * t ^ 2 ∈ P := by
    rw [show c W.a₁ * t + c W.a₃ * t ^ 2 = (c W.a₁ + c W.a₃ * t) * t by ring]
    exact P.mul_mem_left _ ht
  have hR : t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4 ∈ P := by
    rw [show t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4 =
      (1 + c W.a₂ * t + c W.a₄ * t ^ 2 + c W.a₆ * t ^ 3) * t by ring]
    exact P.mul_mem_left _ ht
  have heq := infinityZInt_equation W K
  dsimp only at heq
  have hz2 : z ^ 2 ∈ P := by
    rw [show z ^ 2 =
      (t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4) -
        (c W.a₁ * t + c W.a₃ * t ^ 2) * z by linear_combination heq]
    exact P.sub_mem hR (by simpa [mul_comm] using P.mul_mem_left z hBt)
  have hz : z ∈ P := by
    have hzz : z * z ∈ P := by simpa [pow_two] using hz2
    exact (v.isPrime.mem_or_mem hzz).elim id id
  have ht2 : t ∈ P ^ 2 := by
    rw [pow_two]
    have hzz : z ^ 2 ∈ P * P := by
      simpa [pow_two] using Ideal.mul_mem_mul hz hz
    have hBz : (c W.a₁ * t + c W.a₃ * t ^ 2) * z ∈ P * P :=
      Ideal.mul_mem_mul hBt hz
    have hhigh : c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4 ∈ P * P := by
      rw [show c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4 =
        (c W.a₂ + c W.a₄ * t + c W.a₆ * t ^ 2) * (t * t) by ring]
      exact (P * P).mul_mem_left _ (Ideal.mul_mem_mul ht ht)
    rw [show t = z ^ 2 + (c W.a₁ * t + c W.a₃ * t ^ 2) * z -
      (c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4) by
        linear_combination -heq]
    exact (P * P).sub_mem ((P * P).add_mem hzz hBz) hhigh
  rw [maximalIdeal_infty_eq_span_t k, Ideal.map_span, Set.image_singleton, Ideal.span_le]
  rintro _ rfl
  exact ht2
end
end WeierstrassCurve.Affine.Chart
end
end
open FunctionField
open FunctionField.Chart
open Polynomial
open scoped Polynomial RatFunc
open WeierstrassCurve.Affine.Chart
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
attribute [local instance] WeierstrassCurve.Affine.Chart.instNoZeroSMulDivisorsInfinity
attribute [local instance] WeierstrassCurve.Affine.Chart.instInfinityConstantsTower
include W
omit [WeierstrassCurve.IsElliptic W]
namespace WeierstrassCurve.Affine.Chart
theorem _root_.solution
    (v : IsDedekindDomain.HeightOneSpectrum S∞) :
    (IsLocalRing.maximalIdeal A∞).ramificationIdx' v.asIdeal = 2 := by
  let p := IsLocalRing.maximalIdeal A∞
  let P := v.asIdeal
  have hle2 : Ideal.map (algebraMap A∞ S∞) p ≤ P ^ 2 :=
    infinity_map_maximalIdeal_le_sq W K v
  have hpP : Ideal.map (algebraMap A∞ S∞) p ≤ P :=
    hle2.trans (Ideal.pow_le_self (by omega))
  have hne1 : p.ramificationIdx' P ≠ 1 :=
    (Ideal.ramificationIdx'_ne_one_iff hpP).2 hle2
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  have hunder : P.under A∞ = p :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A∞ P)
  letI : P.LiesOver p := ⟨hunder.symm⟩
  have hne0 : p.ramificationIdx' P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (S := S∞) P hp0
  have hle : p.ramificationIdx' P ≤ Module.finrank k⟮X⟯ K :=
    Ideal.ramificationIdx_le_finrank (S := S∞) (K := k⟮X⟯) (L := K) P
  rw [W.finrank_ratFunc_eq_two K] at hle
  change p.ramificationIdx' P = 2
  omega
end WeierstrassCurve.Affine.Chart
