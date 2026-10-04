-- Prove2me | solution 1 for SennottDP.ResidualLife.bmrl_finite_moments
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:46:59.996683+00:00
-- url     : https://prove2.me/submissions/65488ed8-5d79-4680-8e6a-9e945a0627e1

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist
import Theorems.Thm_SennottDP_ResidualLife_moments_via_tail
import Theorems.Thm_SennottDP_ResidualLife_moment_finite_iff_tail

open scoped ENNReal NNReal

namespace SennottDP.ResidualLife

theorem bmrl_tail_anti (u : ℕ → ℝ≥0∞) {s t : ℕ} (h : s ≤ t) : tail u t ≤ tail u s := by
  unfold tail
  refine ENNReal.tsum_le_tsum fun w => ?_
  split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | omega

theorem bmrl_tail_le_one (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (s : ℕ) : tail u s ≤ 1 := by
  rw [← hu.1]
  refine ENNReal.tsum_le_tsum fun w => ?_
  split_ifs <;> simp

theorem bmrl_shift (g : ℕ → ℝ≥0∞) (s : ℕ) :
    ∑' y, (if s ≤ y then g y else 0) = ∑' i, g (s + i) := by
  have hsupp : Function.support (fun y => if s ≤ y then g y else 0) ⊆ Set.range (fun i => i + s) := by
    intro y hy
    by_cases h : s ≤ y
    · exact ⟨y - s, Nat.sub_add_cancel h⟩
    · rw [Function.mem_support] at hy; exact (hy (by simp [h])).elim
  rw [← (add_left_injective s).tsum_eq hsupp]
  refine tsum_congr fun i => ?_
  rw [if_pos (Nat.le_add_left s i), add_comm]

/-- `∑_{i ≥ 0} F*(s+i) = ∑_{y ≥ 1} y u_{s+y}`. -/
theorem bmrl_tail_sum (u : ℕ → ℝ≥0∞) (s : ℕ) :
    ∑' i, tail u (s + i) = ∑' y : ℕ, (y : ℝ≥0∞) * u (s + y) := by
  unfold tail
  rw [ENNReal.tsum_comm]
  have h1 : ∀ w, ∑' i, (if s + i < w then u w else 0) = ((w - s : ℕ) : ℝ≥0∞) * u w := by
    intro w
    rw [tsum_eq_sum (s := Finset.range (w - s))]
    · rw [Finset.sum_congr rfl (fun i hi => if_pos (by
        have := Finset.mem_range.mp hi; omega)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro i hi
      rw [if_neg]
      intro h; exact hi (Finset.mem_range.mpr (by omega))
  simp_rw [h1]
  have h2 : ∀ w, ((w - s : ℕ) : ℝ≥0∞) * u w = if s ≤ w then ((w - s : ℕ) : ℝ≥0∞) * u w else 0 := by
    intro w
    split_ifs with h
    · rfl
    · rw [show w - s = 0 by omega]; simp
  rw [tsum_congr h2]
  rw [bmrl_shift (fun w => ((w - s : ℕ) : ℝ≥0∞) * u w) s]
  refine tsum_congr fun i => ?_
  rw [Nat.add_sub_cancel_left]

theorem bmrl_A (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (U : ℝ≥0) (hB : IsBMRL u U) (s : ℕ) :
    ∑' i, tail u (s + i) ≤ U * tail u s := by
  by_cases h0 : tail u s = 0
  · have : ∀ i, tail u (s + i) = 0 := fun i =>
      le_antisymm (h0 ▸ bmrl_tail_anti u (Nat.le_add_right s i)) bot_le
    simp [this]
  · have hpos : 0 < tail u s := pos_iff_ne_zero.mpr h0
    have htop : tail u s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (bmrl_tail_le_one u hu s)
    have hb := hB s hpos
    rw [bmrl_tail_sum]
    have hterm : ∀ y : ℕ, (y : ℝ≥0∞) * u (s + y) =
        ((y : ℝ≥0∞) ^ 1 * residualDist u s y) * tail u s := by
      intro y
      unfold residualDist
      split_ifs with hy
      · rw [pow_one, mul_assoc, ENNReal.div_mul_cancel h0 htop]
      · rw [show y = 0 by omega]; simp
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right]
    gcongr
    exact hb

/-- `M n = ∑_y C(y,n) F*(y)`. -/
noncomputable def bmrlM (u : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∑' y, ((y.choose n : ℕ) : ℝ≥0∞) * tail u y

theorem bmrl_hockey (y n : ℕ) : ∑ s ∈ Finset.range y, s.choose n = y.choose (n + 1) := by
  induction y with
  | zero => simp
  | succ y ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ', add_comm]

theorem bmrl_B (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (U : ℝ≥0) (hB : IsBMRL u U) (n : ℕ) :
    bmrlM u (n + 1) ≤ U * bmrlM u n := by
  unfold bmrlM
  have e1 : ∀ y, ((y.choose (n + 1) : ℕ) : ℝ≥0∞) * tail u y =
      ∑' s, (if s < y then ((s.choose n : ℕ) : ℝ≥0∞) * tail u y else 0) := by
    intro y
    rw [← bmrl_hockey, Nat.cast_sum, Finset.sum_mul, tsum_eq_sum (s := Finset.range y)]
    · exact Finset.sum_congr rfl fun s hs => (if_pos (Finset.mem_range.mp hs)).symm
    · intro s hs; rw [if_neg (fun h => hs (Finset.mem_range.mpr h))]
  simp_rw [e1]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  calc ∑' y, (if s < y then ((s.choose n : ℕ) : ℝ≥0∞) * tail u y else 0)
      ≤ ∑' y, ((s.choose n : ℕ) : ℝ≥0∞) * (if s ≤ y then tail u y else 0) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        split_ifs with h1 h2
        · exact le_rfl
        · omega
        · exact bot_le
        · exact bot_le
    _ = ((s.choose n : ℕ) : ℝ≥0∞) * ∑' i, tail u (s + i) := by
        rw [ENNReal.tsum_mul_left, bmrl_shift]
    _ ≤ ((s.choose n : ℕ) : ℝ≥0∞) * (U * tail u s) := by gcongr; exact bmrl_A u hu U hB s
    _ = (U : ℝ≥0∞) * (((s.choose n : ℕ) : ℝ≥0∞) * tail u s) := by ring

theorem bmrl_M_le (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (U : ℝ≥0) (hB : IsBMRL u U) (n : ℕ) :
    bmrlM u n ≤ (U : ℝ≥0∞) ^ (n + 1) := by
  induction n with
  | zero =>
    unfold bmrlM
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add, pow_one]
    calc ∑' y, tail u y = ∑' i, tail u (0 + i) := by simp
      _ ≤ U * tail u 0 := bmrl_A u hu U hB 0
      _ ≤ U * 1 := by gcongr; exact bmrl_tail_le_one u hu 0
      _ = U := mul_one _
  | succ n ih =>
    calc bmrlM u (n + 1) ≤ U * bmrlM u n := bmrl_B u hu U hB n
      _ ≤ U * (U : ℝ≥0∞) ^ (n + 1) := by gcongr
      _ = (U : ℝ≥0∞) ^ (n + 1 + 1) := by ring

theorem bmrl_pow_le (y n : ℕ) : y ^ n ≤ n.factorial * (y + n).choose n := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  calc y ^ n ≤ (y + n + 1 - n) ^ n := Nat.pow_le_pow_left (by omega) n
    _ ≤ (y + n).descFactorial n := Nat.pow_sub_le_descFactorial _ _

theorem bmrl_D (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (U : ℝ≥0) (hB : IsBMRL u U) (n : ℕ) :
    ∑' y : ℕ, (y : ℝ≥0∞) ^ n * tail u y < ∞ := by
  have hle : ∀ y : ℕ, (y : ℝ≥0∞) ^ n * tail u y ≤
      (n.factorial : ℝ≥0∞) * ∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
        ((n.choose ij.2 : ℕ) : ℝ≥0∞) * (((y.choose ij.1 : ℕ) : ℝ≥0∞) * tail u y) := by
    intro y
    have h1 : ((y ^ n : ℕ) : ℝ≥0∞) ≤ ((n.factorial * (y + n).choose n : ℕ) : ℝ≥0∞) := by
      exact_mod_cast bmrl_pow_le y n
    rw [Nat.add_choose_eq] at h1
    push_cast at h1
    calc (y : ℝ≥0∞) ^ n * tail u y ≤ ((n.factorial : ℝ≥0∞) * ∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
          ((y.choose ij.1 : ℕ) : ℝ≥0∞) * ((n.choose ij.2 : ℕ) : ℝ≥0∞)) * tail u y := by
          gcongr
      _ = _ := by
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun ij _ => ?_
          ring
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
  rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.mul_lt_top (by simp) ?_
  refine ENNReal.sum_lt_top.mpr fun ij _ => ?_
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_lt_top (by simp) ?_
  exact lt_of_le_of_lt (bmrl_M_le u hu U hB ij.1) (ENNReal.pow_lt_top ENNReal.coe_lt_top)

end SennottDP.ResidualLife

open SennottDP.ResidualLife in
theorem solution (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (hbmrl : IsBMRLDist u) :
    ∀ k : ℕ, moment u k < ∞ := by
  obtain ⟨U, hB⟩ := hbmrl
  intro k
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · unfold moment; simp [hu.1]
    · rw [(moments_via_tail u hu).1]
      have := bmrl_D u hu U hB 0
      simpa using this
  · rw [moment_finite_iff_tail u hu k hk]
    exact bmrl_D u hu U hB (k - 1)


