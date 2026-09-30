-- Prove2me | solution 1 for TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:00.383303+00:00
-- url     : https://prove2.me/submissions/e55952e1-122b-4f40-9a61-ea16e06ada94

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Analytic continuation of an L-series from a bound on its partial sums

If the partial sums `A(n) = ∑_{k=1}^n f k` of a sequence `f : ℕ → ℂ` are `O(n ^ r)`, Mathlib's
`LSeries_eq_mul_integral` (from `Mathlib/NumberTheory/LSeries/SumCoeff.lean`)
writes the L-series of `f` as

`LSeries f s = s * ∫ t in Set.Ioi 1, A(⌊t⌋₊) * t ^ (-(s + 1))`

wherever `LSeries f` converges and `r < Re s`. The right-hand side makes sense on the whole
half-plane `r < Re s`, independently of the convergence of the series, and this file proves that it
is holomorphic there: it is `s` times the Mellin transform of the step function `t ↦ A(⌊t⌋₊)`
at `-s`, and Mathlib's `mellin_differentiableAt_of_isBigO_rpow` applies because the step function
vanishes on `(0, 1)` and is `O(t ^ r)` at infinity.

Together the two statements continue `LSeries f` analytically from its half-plane of convergence
to `Re s > r`; this is the classical continuation of a Dirichlet series with cancelling
coefficients by partial summation (see e.g. Tenenbaum, *Introduction to Analytic and
Probabilistic Number Theory*, Chapter II.1).

## Main results

* `TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO`: under the bound `A(n) = O(n ^ r)`,
  the function `s ↦ s * ∫ t in Set.Ioi 1, A(⌊t⌋₊) * t ^ (-(s + 1))` is
  complex-differentiable on `{s | r < s.re}`.
-/

 section

open Finset Filter MeasureTheory Complex Asymptotics

open scoped Topology

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

/-- The step function `t ↦ ∑_{k=1}^{⌊t⌋₊} f k` vanishes below `1`. -/
private theorem TauCeti.LSeries.sum_Icc_one_natFloor_eq_zero (f : ℕ → ℂ) {t : ℝ} (ht : t < 1) :
    ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, f k = 0 := by
  simp [Nat.floor_eq_zero.mpr ht]

/-- The integral in `LSeries_eq_mul_integral` is a Mellin transform of the partial-sum step
function, evaluated at `-s`. -/
private theorem TauCeti.LSeries.integral_Ioi_one_eq_mellin (f : ℕ → ℂ) (s : ℂ) :
    ∫ t in _root_.Set.Ioi (1 : ℝ), (∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) =
      _root_.mellin (fun t : ℝ ↦ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, f k) (-s) := by
  set A : ℝ → ℂ := fun t ↦ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, f k
  have hEq : _root_.Set.EqOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) • A t)
      ((_root_.Set.Ici (1 : ℝ)).indicator fun t ↦ A t * (t : ℂ) ^ (-(s + 1))) (_root_.Set.Ioi 0) := by
    intro t _
    dsimp only
    by_cases h1 : 1 ≤ t
    · rw [_root_.Set.indicator_of_mem (Set.mem_Ici.mpr h1), _root_.smul_eq_mul, _root_.mul_comm, _root_.neg_add']
    · have hA : A t = 0 := _root_.TauCeti.LSeries.sum_Icc_one_natFloor_eq_zero f (not_le.mp h1)
      rw [_root_.Set.indicator_of_notMem (by simpa using h1), hA, _root_.smul_zero]
  rw [_root_.mellin, _root_.MeasureTheory.setIntegral_congr_fun _root_.measurableSet_Ioi hEq,
    _root_.MeasureTheory.setIntegral_indicator _root_.measurableSet_Ici,
    Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr _root_.zero_lt_one), _root_.MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- **Holomorphy of the partial-summation integral.** If the partial sums
`∑ k ∈ Icc 1 n, f k` are `O(n ^ r)`, then
`s ↦ s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))` is complex-differentiable
on the half-plane `r < Re s`.

By Mathlib's `LSeries_eq_mul_integral` this function agrees with `LSeries f` wherever the series
converges in that half-plane, so it is an analytic continuation of `LSeries f` to `Re s > r`. -/
theorem solution (f : ℕ → ℂ) {r : ℝ}
    (hO : (fun n ↦ ∑ k ∈ _root_.Finset.Icc 1 n, f k) =O[_root_.Filter.atTop] fun n ↦ (n : ℝ) ^ r) :
    _root_.DifferentiableOn ℂ
      (fun s : ℂ ↦ s * ∫ t in _root_.Set.Ioi (1 : ℝ), (∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} := by
  set A : ℝ → ℂ := fun t ↦ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, f k
  have hloc : _root_.MeasureTheory.LocallyIntegrableOn A (_root_.Set.Ioi 0) := by
    simpa [A] using (_root_.locallyIntegrableOn_mul_sum_Icc f _root_.le_rfl (m := 1)
      (g := fun _ ↦ (1 : ℂ)) (_root_.MeasureTheory.locallyIntegrableOn_const 1)).mono_set _root_.Set.Ioi_subset_Ici_self
  have htop : A =O[_root_.Filter.atTop] (· ^ (-(-r))) := by
    simp_rw [_root_.neg_neg]
    have hmax : (fun t : ℝ ↦ _root_.Max.max t 0) =ᶠ[_root_.Filter.atTop] fun t ↦ t := by
      filter_upwards [_root_.Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact _root_.max_eq_left ht
    have hequiv : (fun t : ℝ ↦ (⌊t⌋₊ : ℝ)) ~[_root_.Filter.atTop] fun t ↦ _root_.Max.max t 0 :=
      isEquivalent_nat_floor.congr_right hmax.symm
    exact (hO.comp_tendsto _root_.tendsto_nat_floor_atTop).trans <|
      (hequiv.rpow fun _ ↦ _root_.le_max_right _ _).isBigO.congr' _root_.Filter.EventuallyEq.rfl
        (hmax.fun_comp fun t ↦ t ^ r)
  have hbot (b : ℝ) : A =O[𝓝[>] 0] (· ^ (-b)) := by
    refine (_root_.Asymptotics.isBigO_zero _ _).congr' ?_ _root_.Filter.EventuallyEq.rfl
    filter_upwards [_root_.Ioo_mem_nhdsGT _root_.zero_lt_one] with t ht
    exact (_root_.TauCeti.LSeries.sum_Icc_one_natFloor_eq_zero f ht.2).symm
  intro s hs
  have hmellin : _root_.DifferentiableAt ℂ (fun z : ℂ ↦ _root_.mellin A (-z)) s :=
    (_root_.mellin_differentiableAt_of_isBigO_rpow hloc htop (by simpa using hs) (hbot ((-s).re - 1))
      (by linarith)).comp s differentiableAt_id.neg
  simp_rw [_root_.TauCeti.LSeries.integral_Ioi_one_eq_mellin]
  exact (differentiableAt_id.mul hmellin).differentiableWithinAt

end TauCeti.LSeries

end
end
