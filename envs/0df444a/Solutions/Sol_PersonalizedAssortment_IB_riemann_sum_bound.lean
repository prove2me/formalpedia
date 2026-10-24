-- Prove2me | solution 1 for PersonalizedAssortment.IB.riemann_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:48:04.104518+00:00
-- url     : https://prove2.me/submissions/ccb9ba19-cc43-4d44-b035-04a13199b413

import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MeasureTheory PersonalizedAssortment.IB

theorem solution (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ) (c : ℕ) (hc : 0 < c)
    (I : ℕ) (hI : I < c) :
    1 / (c : ℝ) * ∑ k ∈ Finset.Ioc I c, Ψ ((k : ℝ) / (c : ℝ)) ≤
      1 / (c : ℝ) + ∫ y in ((I : ℝ) + 1) / (c : ℝ)..1, Ψ y := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hcR
  have hmono : MonotoneOn Ψ (Set.Icc 0 1) := hΨ.2.1
  have hint : IntervalIntegrable Ψ volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hmono
  have hcoords (k : ℕ) (hk : k < c) :
      0 ≤ (k : ℝ) / c ∧ (k : ℝ) / c ≤ ((k + 1 : ℕ) : ℝ) / c ∧
        ((k + 1 : ℕ) : ℝ) / c ≤ 1 := by
    refine ⟨by positivity, ?_, ?_⟩
    · apply div_le_div_of_nonneg_right _ hcR.le
      exact_mod_cast Nat.le_succ k
    · apply (div_le_one hcR).mpr
      exact_mod_cast Nat.succ_le_of_lt hk
  have hintk (k : ℕ) (hk : k < c) :
      IntervalIntegrable Ψ volume ((k : ℝ) / c) (((k + 1 : ℕ) : ℝ) / c) := by
    rcases hcoords k hk with ⟨hk0, hk1, hk2⟩
    apply hint.mono_set
    rw [Set.uIcc_of_le hk1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc hk0 hk2
  have hpiece (k : ℕ) (hk : k < c) :
      1 / (c : ℝ) * Ψ ((k : ℝ) / c) ≤
        ∫ y in (k : ℝ) / c..((k + 1 : ℕ) : ℝ) / c, Ψ y := by
    rcases hcoords k hk with ⟨hk0, hk1, hk2⟩
    have hb := intervalIntegral.integral_mono_on hk1
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Ψ ((k : ℝ) / c)) volume _ _)
      (hintk k hk) (fun y hy => hmono ⟨hk0, hk1.trans hk2⟩
        ⟨hk0.trans hy.1, hy.2.trans hk2⟩ hy.1)
    have hw : ((k + 1 : ℕ) : ℝ) / c - (k : ℝ) / c = 1 / (c : ℝ) := by
      push_cast
      ring
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hw] using hb
  have hmain :
      1 / (c : ℝ) * ∑ k ∈ Finset.Ico (I + 1) c, Ψ ((k : ℝ) / c) ≤
        ∫ y in ((I : ℝ) + 1) / (c : ℝ)..1, Ψ y := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico (I + 1) c,
          ∫ y in (k : ℝ) / c..((k + 1 : ℕ) : ℝ) / c, Ψ y := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k hk => hpiece k (Finset.mem_Ico.mp hk).2
      _ = _ := by
        have ht := intervalIntegral.sum_integral_adjacent_intervals_Ico
          (f := Ψ) (μ := volume) (a := fun k : ℕ => (k : ℝ) / c)
          (Nat.succ_le_of_lt hI) (fun k hk => hintk k hk.2)
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, div_self hc0] using ht
  have hset : Finset.Ioc I c = Finset.Ico (I + 1) (c + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_succ_top (Nat.succ_le_of_lt hI), div_self hc0,
    hΨ.2.2.2, mul_add, mul_one]
  linarith

#print axioms solution
