-- Prove2me | solution 1 for WeierstrassCurve.Affine.placeOfPoint_deg_one
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:59:49.809987+00:00
-- url     : https://prove2.me/submissions/96616333-2488-4f7e-a68a-fc08654999a8

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassGenus
import Theorems.Thm_WeierstrassCurve_Affine_Chart_infinity_ramificationIdx_eq_two
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
open scoped Polynomial RatFunc
namespace WeierstrassCurve.Affine.Chart
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
omit [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
lemma finitePlaceOfAffine_degree {x y : k} (h : W.Nonsingular x y) :
    placeDegree k K (finitePlaceOfAffine W K h) = 1 := by
  let e := coordinateRingEquivIntegers W K
  let I := CoordinateRing.XYIdeal W x (Polynomial.C y)
  let v := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv
    (affineHeightOne W h)
  have hv : v.asIdeal = I.map e.toRingHom := by
    change I.comap e.symm.toRingHom = I.map e.toRingHom
    exact Ideal.comap_symm e.toRingEquiv
  let ek : W.CoordinateRing ≃ₐ[k] ringOfIntegers k K := e.restrictScalars k
  let eqQuot : (W.CoordinateRing ⧸ I) ≃ₐ[k] (ringOfIntegers k K ⧸ v.asIdeal) :=
    Ideal.quotientEquivAlg I v.asIdeal ek hv
  change Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal) = 1
  rw [← eqQuot.toLinearEquiv.finrank_eq]
  let exy := CoordinateRing.quotientXYIdealEquiv (W' := W) (x := x)
    (y := Polynomial.C y) h.1
  rw [exy.toLinearEquiv.finrank_eq]
  exact Module.finrank_self k
include W in
theorem placeOfPoint_deg_one (P : W.Point) :
    placeDegree k K (placeOfPoint W K P) = 1 := by
  cases P with
  | zero => exact infinityPlace_deg_one W K
  | some x y h => exact finitePlaceOfAffine_degree W K h
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
omit [IsFullConstantField k K]
include W
namespace WeierstrassCurve.Affine
theorem _root_.solution (P : W.Point) :
    (placeOfPoint W K P).degree = 1 := by
  rw [placeOfPoint, ← placeDegree_eq]
  exact Chart.placeOfPoint_deg_one W K P
end WeierstrassCurve.Affine
