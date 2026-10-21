-- Prove2me | solution 1 for WeierstrassCurve.Affine.Chart.infinity_heightOne_unique
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:47:23.11209+00:00
-- url     : https://prove2.me/submissions/475b2349-35e0-4789-982d-6d0889396882

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassInfinity
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
attribute [local instance] WeierstrassCurve.Affine.Chart.instInfinityConstantsTower
include W
omit [WeierstrassCurve.IsElliptic W]
namespace WeierstrassCurve.Affine.Chart
theorem _root_.solution
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
  letI : P.LiesOver p := ⟨hPunder.symm⟩
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := P)).2
      ⟨v.isPrime, (show P.LiesOver p from inferInstance)⟩
  letI : Q.LiesOver p := ⟨hQunder.symm⟩
  have hQ : Q ∈ IsDedekindDomain.primesOverFinset p S∞ :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (P := Q)).2
      ⟨w.isPrime, (show Q.LiesOver p from inferInstance)⟩
  by_contra hne
  let g : Ideal S∞ → ℕ := fun R => p.ramificationIdx' R * p.inertiaDeg' R
  let F := IsDedekindDomain.primesOverFinset p S∞
  have hsum : F.sum g = 2 := by
    simpa [F, g] using infinity_sum_ramification_inertia W K
  have hQerase : Q ∈ F.erase P := Finset.mem_erase.2 ⟨Ne.symm hne, hQ⟩
  have hQle : g Q ≤ (F.erase P).sum g :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hQerase
  have hdecomp : (F.erase P).sum g + g P = 2 := by
    calc
      (F.erase P).sum g + g P = F.sum g := Finset.sum_erase_add F g hP
      _ = 2 := hsum
  have heP : p.ramificationIdx' P = 2 := infinity_ramificationIdx_eq_two W K v
  have heQ : p.ramificationIdx' Q = 2 := infinity_ramificationIdx_eq_two W K w
  have hfP : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
  have hfQ : 0 < p.inertiaDeg' Q := Ideal.inertiaDeg'_pos p Q
  dsimp [g] at hQle hdecomp
  rw [heP] at hdecomp
  rw [heQ] at hQle
  omega
end WeierstrassCurve.Affine.Chart
