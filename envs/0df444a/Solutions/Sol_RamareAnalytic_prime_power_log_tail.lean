-- Prove2me | solution 1 for RamareAnalytic.prime_power_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T21:25:57.214525+00:00
-- url     : https://prove2.me/submissions/10f07fa4-5709-4e38-b577-543ede532dbf

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

namespace RamareAnalytic

/-!
Uncompiled draft: quantitative Chebyshev power tails for the weighted Euler
product. The prime-power logarithmic tail is derived from the actual theta
bound and the integral test, without assuming convergence or a prime-tail
estimate. Intended pin: Lean 4.33.1 / Mathlib 0df444a.

Use m=1001, s=8/5 and s=6/5. These are the two power tails required by the
alpha=2/5 Euler factor. The finite factor certificate, division by log(1000),
and final product assembly are deliberately separate from this component.
-/

/-- Decreasing nonnegative weights preserve an inequality of all prefix sums. -/
theorem sum_weighted_le_of_prefix_le
    (a b w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w)
    (hab : ∀ N, (∑ i ∈ Finset.range N, a i) ≤ ∑ i ∈ Finset.range N, b i)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, w i * a i) ≤ ∑ i ∈ Finset.range N, w i * b i := by
  have hparts (c : ℕ → ℝ) :
      (∑ i ∈ Finset.range N, w i * c i) =
      w (N - 1) * (∑ i ∈ Finset.range N, c i) +
        ∑ i ∈ Finset.range (N - 1),
          (w i - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), c j) := by
    have h := Finset.sum_range_by_parts w c N
    simp only [smul_eq_mul] at h
    rw [h, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hparts a, hparts b]
  apply add_le_add (mul_le_mul_of_nonneg_left (hab N) (hw (N - 1)))
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hab (i + 1))
    (sub_nonneg.mpr (hanti (Nat.le_succ i)))

/-- Linear control on shifted prefix sums gives the sharp elementary power-tail constant. -/
theorem shifted_rpow_tail_of_prefix_le
    (a : ℕ → ℝ) (A : ℝ) (m : ℕ) (s : ℝ)
    (hA : 0 ≤ A) (hm : 1 ≤ m) (hs : 1 < s)
    (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ N, (∑ i ∈ Finset.range (N + 1), a i) ≤ A * ((m : ℝ) + (N : ℝ))) :
    Summable (fun i : ℕ => a i * ((m + i : ℕ) : ℝ) ^ (-s)) ∧
      (∑' i : ℕ, a i * ((m + i : ℕ) : ℝ) ^ (-s)) ≤
        A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
  let w : ℕ → ℝ := fun i => ((m + i : ℕ) : ℝ) ^ (-s)
  let b : ℕ → ℝ := fun i => if i = 0 then A * (m : ℝ) else A
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hmR
  have hspos : 0 < s := zero_lt_one.trans hs
  have hsmpos : 0 < s - 1 := sub_pos.mpr hs
  have hsm0 : s - 1 ≠ 0 := hsmpos.ne'
  have hb (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), b i) = A * ((m : ℝ) + (N : ℝ)) := by
    simp [b, Finset.sum_range_succ']
    <;> ring
  have hab : ∀ N, (∑ i ∈ Finset.range N, a i) ≤ ∑ i ∈ Finset.range N, b i := by
    intro N
    cases N with
    | zero => simp
    | succ N => rw [hb]; exact hprefix N
  have hw : ∀ n, 0 ≤ w n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hanti : Antitone w := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · have hmi : 0 < m + i := by omega
      exact_mod_cast hmi
    · exact_mod_cast Nat.add_le_add_left hij m
    · linarith
  have hantiR : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Ici (m : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hmpos.trans_le hx) hxy (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt (show -s < -1 by linarith) hmpos
  have htail (N : ℕ) :
      (∑ i ∈ Finset.range N, w (i + 1)) ≤ (m : ℝ) ^ (1 - s) / (s - 1) := by
    have heq : (∑ i ∈ Finset.Ico m (m + N), (((i + 1 : ℕ) : ℝ) ^ (-s))) =
        ∑ i ∈ Finset.range N, w (i + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, w, Nat.add_assoc]
    rw [← heq]
    calc
      _ ≤ ∫ x : ℝ in Set.Ioi (m : ℝ), x ^ (-s) := by
        apply (hantiR.mono Set.Icc_subset_Ici_self).sum_Ico_le_integral hint
        intro x hx
        exact Real.rpow_nonneg (hmpos.trans hx).le _
      _ = (m : ℝ) ^ (1 - s) / (s - 1) := by
        rw [integral_Ioi_rpow_of_lt (show -s < -1 by linarith) hmpos,
          show -s + 1 = 1 - s by ring]
        have hn : 1 - s ≠ 0 := by linarith
        field_simp
        <;> ring
  have hpower : (m : ℝ) * (m : ℝ) ^ (-s) = (m : ℝ) ^ (1 - s) := by
    rw [show 1 - s = 1 + (-s) by ring, Real.rpow_add hmpos, Real.rpow_one]
  have hweighted_b (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), w i * b i) =
        A * ((m : ℝ) * w 0 + ∑ i ∈ Finset.range N, w (i + 1)) := by
    simp [b, Finset.sum_range_succ']
    rw [← Finset.sum_mul]
    ring
  have hfinite (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), w i * a i) ≤
        A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N + 1), w i * b i :=
        sum_weighted_le_of_prefix_le a b w hw hanti hab (N + 1)
      _ = A * ((m : ℝ) * w 0 + ∑ i ∈ Finset.range N, w (i + 1)) := hweighted_b N
      _ ≤ A * ((m : ℝ) * w 0 + (m : ℝ) ^ (1 - s) / (s - 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (htail N)) hA
      _ = _ := by
        simp only [w, Nat.add_zero, hpower]
        field_simp
        <;> ring
  have hnonneg : ∀ i, 0 ≤ w i * a i := fun i => mul_nonneg (hw i) (ha i)
  have hrange : ∀ N, (∑ i ∈ Finset.range N, w i * a i) ≤
      A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
    intro N
    cases N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
    | succ N => exact hfinite N
  have hsum := summable_of_sum_range_le hnonneg hrange
  have hbound := Real.tsum_le_of_sum_range_le hnonneg hrange
  simpa only [w, mul_comm] using And.intro hsum hbound

/-- Chebyshev's theta estimate bounds prime logarithms weighted by p^(-s).
The index m+k enumerates every integer at least m exactly once. -/
theorem prime_power_log_tail (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 1 < s) :
    Summable (fun k : ℕ =>
      if (m + k).Prime then Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s)
      else 0) ∧
    (∑' k : ℕ, if (m + k).Prime then
      Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s) else 0) ≤
      Real.log 4 * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log (p : ℝ) else 0
  have hc : ∀ n, 0 ≤ c n := by
    intro n
    dsimp only [c]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · exact le_rfl
  have hprefix (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), c (m + i)) ≤ Real.log 4 * ((m : ℝ) + (N : ℝ)) := by
    calc
      _ = ∑ i ∈ Finset.Ico m (m + N + 1), c i := by
        rw [Finset.sum_Ico_eq_sum_range,
          show m + N + 1 - m = N + 1 by omega]
      _ ≤ ∑ i ∈ Finset.range (m + N + 1), c i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
        · intro i hi hi'
          exact hc i
      _ = Chebyshev.theta ((m + N : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
          ← Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
      _ ≤ Real.log 4 * ((m + N : ℕ) : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.cast_add]
  have h := shifted_rpow_tail_of_prefix_le (fun i => c (m + i))
    (Real.log 4) m s (Real.log_nonneg (by norm_num)) hm hs
    (fun i => hc (m + i)) hprefix
  simpa only [c, ite_mul, zero_mul] using h

end RamareAnalytic

theorem solution (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 1 < s) :
    Summable (fun k : ℕ =>
      if (m + k).Prime then Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s)
      else 0) ∧
    (∑' k : ℕ, if (m + k).Prime then
      Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s) else 0) ≤
      Real.log 4 * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
  exact RamareAnalytic.prime_power_log_tail m hm s hs

#print axioms solution
