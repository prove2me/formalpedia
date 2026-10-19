-- Prove2me | solution 1 for RamanujanNotebooks.entry_18_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:39:11.483982+00:00
-- url     : https://prove2.me/submissions/a63ddd72-ec42-4b1c-8b27-601af191800e

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_hyp2F1R
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorialR

namespace RNE18
open RamanujanNotebooks Filter Topology

noncomputable def a (k : ℕ) : ℝ :=
  shiftedFactorialR (-1 / 2) k * shiftedFactorialR (-1 / 2) k /
    (shiftedFactorialR 1 k * (k.factorial : ℝ))

lemma sf_one (k : ℕ) : shiftedFactorialR 1 k = k.factorial := by
  induction k with
  | zero => simp [shiftedFactorialR]
  | succ k ih =>
    rw [shiftedFactorialR, Finset.prod_range_succ, ← shiftedFactorialR, ih, Nat.factorial_succ]
    push_cast; ring

lemma sf_half_le (k : ℕ) : |shiftedFactorialR (-1 / 2) k| ≤ k.factorial := by
  induction k with
  | zero => simp [shiftedFactorialR]
  | succ k ih =>
    rw [shiftedFactorialR, Finset.prod_range_succ, ← shiftedFactorialR, abs_mul, Nat.factorial_succ]
    push_cast
    have h1 : |(-1 / 2 : ℝ) + k| ≤ k + 1 := by
      rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc |shiftedFactorialR (-1 / 2) k| * |(-1 / 2 : ℝ) + k| ≤ k.factorial * (k + 1) :=
          mul_le_mul ih h1 (abs_nonneg _) (by positivity)
      _ = (k + 1) * k.factorial := by ring

lemma a_le (k : ℕ) : |a k| ≤ 1 := by
  rw [a, sf_one, abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < k.factorial)]
  rw [div_le_one (by positivity)]
  exact mul_le_mul (sf_half_le k) (sf_half_le k) (abs_nonneg _) (by positivity)

lemma summ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : Summable (fun k => a k * t ^ k) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one ht0 ht1)
  intro k
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0]
  exact mul_le_of_le_one_left (by positivity) (a_le k)

lemma tail_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    |∑' k, a (k + 6) * t ^ (k + 6)| ≤ 2 * t ^ 6 := by
  have hs : Summable (fun k : ℕ => t ^ (k + 6)) := by
    simp_rw [pow_add]
    exact (summable_geometric_of_lt_one ht0 (by linarith)).mul_right _
  calc |∑' k, a (k + 6) * t ^ (k + 6)| ≤ ∑' k : ℕ, t ^ (k + 6) := by
        rw [← Real.norm_eq_abs]
        refine tsum_of_norm_bounded hs.hasSum (fun k => ?_)
        rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0]
        exact mul_le_of_le_one_left (by positivity) (a_le _)
    _ = t ^ 6 / (1 - t) := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one ht0 (by linarith)]
        ring
    _ ≤ 2 * t ^ 6 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg ht0 6]

lemma a_vals : a 0 = 1 ∧ a 1 = 1 / 4 ∧ a 2 = 1 / 64 ∧ a 3 = 1 / 256 ∧ a 4 = 25 / 16384 ∧
    a 5 = 49 / 65536 := by
  simp only [a, shiftedFactorialR, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [Nat.factorial]

lemma F_eq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    hyp2F1R (-1 / 2) (-1 / 2) 1 t =
      1 + t / 4 + t ^ 2 / 64 + t ^ 3 / 256 + 25 / 16384 * t ^ 4 + 49 / 65536 * t ^ 5 +
        ∑' k, a (k + 6) * t ^ (k + 6) := by
  have h := (summ t ht0 (by linarith)).sum_add_tsum_nat_add 6
  have : hyp2F1R (-1 / 2) (-1 / 2) 1 t = ∑' k, a k * t ^ k := rfl
  rw [this, ← h]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := a_vals
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5]
  ring

theorem main :
    Filter.Tendsto
      (fun t : ℝ =>
        (hyp2F1R (-1 / 2) (-1 / 2) 1 t - (1 + 3 * t / (10 + Real.sqrt (4 - 3 * t)))) / t ^ 5)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3 / 2 ^ 17)) := by
  set p : ℝ → ℝ := fun t => 2 - 3 / 4 * t - 9 / 64 * t ^ 2 - 27 / 512 * t ^ 3 - 405 / 16384 * t ^ 4
  set ρ : ℝ → ℝ := fun t => -1701 / 32768 - 5103 / 524288 * t - 10935 / 4194304 * t ^ 2 -
    164025 / 268435456 * t ^ 3
  set R : ℝ → ℝ := fun t => ∑' k, a (k + 6) * t ^ (k + 6)
  set s : ℝ → ℝ := fun t => Real.sqrt (4 - 3 * t)
  -- the decomposition on (0, 1/2]
  have hdec : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
      (hyp2F1R (-1 / 2) (-1 / 2) 1 t - (1 + 3 * t / (10 + Real.sqrt (4 - 3 * t)))) / t ^ 5 =
        (3 / 4096 + 49 / 65536 * t) / (32 + t) + R t / t ^ 5 + t * ρ t / ((s t + p t) * (32 + t)) := by
    intro t ht0 ht1
    have hs2 : s t ^ 2 = 4 - 3 * t := Real.sq_sqrt (by linarith)
    have hs0 : 0 ≤ s t := Real.sqrt_nonneg _
    have hp0 : 1 < p t := by
      simp only [p]
      nlinarith [pow_pos ht0 2, pow_pos ht0 3, pow_pos ht0 4, pow_le_pow_left₀ ht0.le ht1 2,
        pow_le_pow_left₀ ht0.le ht1 3, pow_le_pow_left₀ ht0.le ht1 4]
    have hr : 4 - 3 * t - p t ^ 2 = t ^ 5 * ρ t := by simp only [p, ρ]; ring
    have hsp : s t = p t + t ^ 5 * ρ t / (s t + p t) := by
      field_simp
      linear_combination hs2 - hr
    rw [F_eq t ht0.le ht1]
    have h10 : 10 + Real.sqrt (4 - 3 * t) ≠ 0 := by positivity
    have ht5 : t ^ 5 ≠ 0 := by positivity
    have h32 : 32 + t ≠ 0 := by linarith
    have hspne : s t + p t ≠ 0 := by linarith
    have hkey : 3 * t / (10 + s t) = t * (10 - s t) / (32 + t) := by
      field_simp
      linear_combination hs2
    change (1 + t / 4 + t ^ 2 / 64 + t ^ 3 / 256 + 25 / 16384 * t ^ 4 + 49 / 65536 * t ^ 5 + R t -
      (1 + 3 * t / (10 + s t))) / t ^ 5 = _
    rw [hkey]
    nth_rewrite 1 [hsp]
    field_simp
    simp only [p, ρ]
    ring
  -- limits
  have hR : Tendsto (fun t => R t / t ^ 5) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hb : Tendsto (fun t : ℝ => 2 * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Tendsto (fun t : ℝ => 2 * t) (nhds 0) (nhds 0) := by
        simpa using (tendsto_id (x := nhds (0 : ℝ))).const_mul (2 : ℝ)
      exact this.mono_left nhdsWithin_le_nhds
    apply squeeze_zero_norm' _ hb
    have : Set.Ioo (0 : ℝ) (1 / 2) ∈ nhdsWithin 0 (Set.Ioi 0) :=
      Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with t ht
    rw [norm_div, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
    rw [div_le_iff₀ (by have := ht.1; positivity)]
    have := tail_le t ht.1.le ht.2.le
    calc |R t| ≤ 2 * t ^ 6 := this
      _ = 2 * t * t ^ 5 := by ring
  have hA : Tendsto (fun t : ℝ => (3 / 4096 + 49 / 65536 * t) / (32 + t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3 / 2 ^ 17)) := by
    have hc : ContinuousAt (fun t : ℝ => (3 / 4096 + 49 / 65536 * t) / (32 + t)) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    convert this using 2; norm_num
  have hB : Tendsto (fun t : ℝ => t * ρ t / ((s t + p t) * (32 + t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : ContinuousAt (fun t : ℝ => t * ρ t / ((s t + p t) * (32 + t))) 0 := by
      apply ContinuousAt.div (by fun_prop)
      · simp only [s, p]; fun_prop
      · simp only [s, p]; norm_num
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have hsum := (hA.add hR).add hB
  rw [add_zero, add_zero] at hsum
  apply hsum.congr'
  have : Set.Ioc (0 : ℝ) (1 / 2) ∈ nhdsWithin 0 (Set.Ioi 0) :=
    mem_of_superset (Ioo_mem_nhdsGT (by norm_num)) Set.Ioo_subset_Ioc_self
  filter_upwards [this] with t ht
  exact (hdec t ht.1 ht.2).symm

end RNE18

open RamanujanNotebooks in
theorem solution :
    Filter.Tendsto
      (fun t : ℝ =>
        (hyp2F1R (-1 / 2) (-1 / 2) 1 t - (1 + 3 * t / (10 + Real.sqrt (4 - 3 * t)))) / t ^ 5)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3 / 2 ^ 17)) :=
  RNE18.main
