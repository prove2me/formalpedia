-- Prove2me | solution 1 for StrictCompatLB.MeanField.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:39:22.056505+00:00
-- url     : https://prove2.me/submissions/c8bb703f-d2dd-48fa-b4ef-a4029bff3087

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Policy

open Filter Topology Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField.L42

open StrictCompatLB.MeanField

lemma pow_diff (a a' : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ha' : 0 ≤ a') (ha1' : a' ≤ 1) (n : ℕ) :
    |a ^ n - a' ^ n| ≤ n * |a - a'| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - a' ^ (n + 1) = a * (a ^ n - a' ^ n) + a' ^ n * (a - a') := by ring
    rw [e]
    have h1 : |a * (a ^ n - a' ^ n)| ≤ |a ^ n - a' ^ n| := by
      rw [abs_mul, abs_of_nonneg ha]
      exact mul_le_of_le_one_left (abs_nonneg _) ha1
    have h2 : |a' ^ n * (a - a')| ≤ |a - a'| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg ha' n)]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ha' ha1')
    calc _ ≤ |a * (a ^ n - a' ^ n)| + |a' ^ n * (a - a')| := abs_add_le _ _
      _ ≤ n * |a - a'| + |a - a'| := by linarith
      _ = _ := by push_cast; ring

lemma mono_diff (a b a' b' : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ha' : 0 ≤ a') (ha1' : a' ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hb' : 0 ≤ b') (hb1' : b' ≤ 1) (k m : ℕ) :
    |a ^ k * b ^ m - a' ^ k * b' ^ m| ≤ k * |a - a'| + m * |b - b'| := by
  have e : a ^ k * b ^ m - a' ^ k * b' ^ m = (a ^ k - a' ^ k) * b ^ m + a' ^ k * (b ^ m - b' ^ m) := by
    ring
  rw [e]
  have h1 : |(a ^ k - a' ^ k) * b ^ m| ≤ k * |a - a'| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hb m)]
    calc _ ≤ |a ^ k - a' ^ k| := mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hb hb1)
      _ ≤ _ := pow_diff a a' ha ha1 ha' ha1' k
  have h2 : |a' ^ k * (b ^ m - b' ^ m)| ≤ m * |b - b'| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ha' k)]
    calc _ ≤ |b ^ m - b' ^ m| := mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ha' ha1')
      _ ≤ _ := pow_diff b b' hb hb1 hb' hb1' m
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

lemma key (a b a' b' D : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ha' : 0 ≤ a') (ha1' : a' ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hb' : 0 ≤ b') (hb1' : b' ≤ 1)
    (hDa : |a - a'| ≤ D) (hDb : |b - b'| ≤ D) (hy : 0 ≤ a' - b') (d : ℕ) :
    |(a ^ d - b ^ d) - (a' ^ d - b' ^ d)| ≤
      d * |(a - b) - (a' - b')| + (d : ℝ) ^ 2 * D * (a' - b') := by
  set h := ∑ i ∈ range d, a ^ i * b ^ (d - 1 - i) with hh
  set h' := ∑ i ∈ range d, a' ^ i * b' ^ (d - 1 - i) with hh'
  have e1 := geom_sum₂_mul a b d
  have e2 := geom_sum₂_mul a' b' d
  have e : (a ^ d - b ^ d) - (a' ^ d - b' ^ d) =
      h * ((a - b) - (a' - b')) + (h - h') * (a' - b') := by
    rw [← e1, ← e2]; ring
  rw [e]
  have hD : 0 ≤ D := le_trans (abs_nonneg _) hDa
  have hbound : |h| ≤ d := by
    calc |h| ≤ ∑ i ∈ range d, |a ^ i * b ^ (d - 1 - i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range d, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_of_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))]
          exact mul_le_one₀ (pow_le_one₀ ha ha1) (pow_nonneg hb _) (pow_le_one₀ hb hb1)
      _ = d := by simp
  have hdiff : |h - h'| ≤ (d : ℝ) ^ 2 * D := by
    rw [hh, hh', ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ i ∈ range d, |a ^ i * b ^ (d - 1 - i) - a' ^ i * b' ^ (d - 1 - i)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range d, ((d : ℝ) * D) := by
          apply Finset.sum_le_sum; intro i hi
          have hi' := mem_range.mp hi
          calc _ ≤ (i : ℝ) * |a - a'| + ((d - 1 - i : ℕ) : ℝ) * |b - b'| :=
                mono_diff a b a' b' ha ha1 ha' ha1' hb hb1 hb' hb1' i (d - 1 - i)
            _ ≤ (i : ℝ) * D + ((d - 1 - i : ℕ) : ℝ) * D := by gcongr
            _ = ((i + (d - 1 - i) : ℕ) : ℝ) * D := by push_cast; ring
            _ ≤ (d : ℝ) * D := by
                gcongr
                exact_mod_cast (by omega : i + (d - 1 - i) ≤ d)
      _ = (d : ℝ) ^ 2 * D := by simp; ring
  calc _ ≤ |h * ((a - b) - (a' - b'))| + |(h - h') * (a' - b')| := abs_add_le _ _
    _ = |h| * |(a - b) - (a' - b')| + |h - h'| * (a' - b') := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy]
    _ ≤ _ := by gcongr

section tails
variable {x : ℕ → ℝ}

lemma tail_summable (hx : InX x) (i : ℕ) : Summable (fun j => if i ≤ j then x j else 0) :=
  Summable.of_nonneg_of_le (fun j => by split_ifs; exact hx.1 j; exact le_refl _)
    (fun j => by split_ifs; exact le_refl _; exact hx.1 j) hx.2.summable

lemma tail_nonneg (hx : InX x) (i : ℕ) : 0 ≤ tailOf x i :=
  tsum_nonneg (fun j => by split_ifs; exact hx.1 j; exact le_refl _)

lemma tail_le_one (hx : InX x) (i : ℕ) : tailOf x i ≤ 1 := by
  rw [← hx.2.tsum_eq]
  exact Summable.tsum_le_tsum (fun j => by split_ifs; exact le_refl _; exact hx.1 j)
    (tail_summable hx i) hx.2.summable

lemma tail_sub (hx : InX x) (i : ℕ) : tailOf x i - tailOf x (i + 1) = x i := by
  have : tailOf x i = ∑' j, ((if i + 1 ≤ j then x j else 0) + (if j = i then x j else 0)) := by
    unfold tailOf
    congr 1; funext j
    by_cases h1 : j = i
    · subst h1; simp
    · by_cases h2 : i ≤ j
      · rw [if_pos h2, if_pos (by omega), if_neg h1, add_zero]
      · rw [if_neg h2, if_neg (by omega), if_neg h1, add_zero]
  rw [this, Summable.tsum_add (tail_summable hx (i + 1))
    (summable_of_ne_finset_zero (s := {i}) (fun b hb => by
      rw [if_neg (by simpa using hb)])), tsum_ite_eq]
  unfold tailOf; ring

lemma tail_diff {y : ℕ → ℝ} (hx : InX x) (hy : InX y) (i : ℕ) :
    |tailOf x i - tailOf y i| ≤ ∑' j, |x j - y j| := by
  have hs : Summable (fun j => |x j - y j|) := (hx.2.summable.sub hy.2.summable).abs
  have e : tailOf x i - tailOf y i = ∑' j, (if i ≤ j then x j - y j else 0) := by
    unfold tailOf
    rw [← Summable.tsum_sub (tail_summable hx i) (tail_summable hy i)]
    congr 1; funext j; split_ifs <;> ring
  have hs2 : Summable (fun j => if i ≤ j then x j - y j else 0) := by
    have := (tail_summable hx i).sub (tail_summable hy i)
    refine this.congr (fun j => ?_)
    split_ifs <;> ring
  rw [e, abs_le]
  constructor
  · rw [← tsum_neg]
    exact Summable.tsum_le_tsum (fun j => by
      split_ifs
      · exact neg_abs_le _
      · simp) hs.neg hs2
  · exact Summable.tsum_le_tsum (fun j => by
      split_ifs
      · exact le_abs_self _
      · exact abs_nonneg _) hs2 hs

end tails

end StrictCompatLB.MeanField.L42

open StrictCompatLB.MeanField StrictCompatLB.MeanField.L42 in
theorem solution (d : ℕ) (hd : 1 ≤ d) :
    IsLipschitzPolicyWith (jsqdAssign d) (2 * (d.factorial : ℝ) * (d : ℝ) ^ 2) := by
  intro x y hx hy
  set D := ∑' j, |x j - y j| with hD
  have hs : Summable (fun j => |x j - y j|) := (hx.2.summable.sub hy.2.summable).abs
  have hD0 : 0 ≤ D := tsum_nonneg (fun j => abs_nonneg _)
  have hl : PowerOfDUniversality.Fluid.l1dist x y = ENNReal.ofReal D := by
    unfold PowerOfDUniversality.Fluid.l1dist
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => abs_nonneg _) hs]
  have term : ∀ i, |jsqdAssign d x i - jsqdAssign d y i| ≤
      d * |x i - y i| + (d : ℝ) ^ 2 * D * y i := by
    intro i
    unfold jsqdAssign
    have h1 := tail_sub hx i
    have h2 := tail_sub hy i
    have := key (tailOf x i) (tailOf x (i + 1)) (tailOf y i) (tailOf y (i + 1)) D
      (tail_nonneg hx i) (tail_le_one hx i) (tail_nonneg hy i) (tail_le_one hy i)
      (tail_nonneg hx _) (tail_le_one hx _) (tail_nonneg hy _) (tail_le_one hy _)
      (tail_diff hx hy i) (tail_diff hx hy (i + 1)) (by rw [h2]; exact hy.1 i) d
    rw [h1, h2] at this
    exact this
  have hs2 : Summable (fun i => (d : ℝ) * |x i - y i| + (d : ℝ) ^ 2 * D * y i) :=
    (hs.mul_left _).add (hy.2.summable.mul_left _)
  have hnn : ∀ i, 0 ≤ (d : ℝ) * |x i - y i| + (d : ℝ) ^ 2 * D * y i := fun i =>
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      (mul_nonneg (mul_nonneg (sq_nonneg _) hD0) (hy.1 i))
  have hsum : ∑' i, ((d : ℝ) * |x i - y i| + (d : ℝ) ^ 2 * D * y i) = d * D + (d : ℝ) ^ 2 * D := by
    rw [Summable.tsum_add (hs.mul_left _) (hy.2.summable.mul_left _),
      Summable.tsum_mul_left _ hs, Summable.tsum_mul_left _ hy.2.summable, hy.2.tsum_eq]
    ring
  rw [hl]
  unfold PowerOfDUniversality.Fluid.l1dist
  calc ∑' i, ENNReal.ofReal |jsqdAssign d x i - jsqdAssign d y i|
      ≤ ∑' i, ENNReal.ofReal ((d : ℝ) * |x i - y i| + (d : ℝ) ^ 2 * D * y i) :=
        ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal (term i))
    _ = ENNReal.ofReal (d * D + (d : ℝ) ^ 2 * D) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs2, hsum]
    _ ≤ ENNReal.ofReal (2 * (d.factorial : ℝ) * (d : ℝ) ^ 2 * D) := by
        apply ENNReal.ofReal_le_ofReal
        have hf : (1 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d)
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
        have h3 : (d : ℝ) * D ≤ (d : ℝ) ^ 2 * D := mul_le_mul_of_nonneg_right this hD0
        have h4 : 2 * (d : ℝ) ^ 2 * D ≤ 2 * (d.factorial : ℝ) * (d : ℝ) ^ 2 * D := by
          have : 0 ≤ (d : ℝ) ^ 2 * D := mul_nonneg (sq_nonneg _) hD0
          nlinarith
        linarith
    _ = ENNReal.ofReal (2 * (d.factorial : ℝ) * (d : ℝ) ^ 2) * ENNReal.ofReal D := by
        rw [← ENNReal.ofReal_mul (by positivity)]
