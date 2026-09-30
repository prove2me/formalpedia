-- Prove2me | solution 1 for automatic_sequence_irrationality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:18:54.425891+00:00
-- url     : https://prove2.me/submissions/f611139e-b73a-4ac8-9138-ec91fea45e99

import Mathlib

set_option autoImplicit false

-- Port of ryanshin's accepted legacy proof a1658666-3409-46a7-91fd-59b30131b954.

namespace AutomaticDigits

theorem avoids_all_positions (n : ℕ)
    (h : ∀ k ≤ Nat.log 2 (n + 1), (n / 2 ^ k) % 4 ≠ 2) :
    ∀ k : ℕ, (n / 2 ^ k) % 4 ≠ 2 := by
  intro k
  by_cases hk : k ≤ Nat.log 2 (n + 1)
  · exact h k hk
  · have hpow : n + 1 < 2 ^ k :=
      Nat.lt_pow_of_log_lt Nat.one_lt_two (Nat.lt_of_not_ge hk)
    have hdiv : n / 2 ^ k = 0 :=
      Nat.div_eq_of_lt (lt_trans (Nat.lt_succ_self n) hpow)
    simp [hdiv]

theorem quotient_avoids (n : ℕ) (h : ∀ k : ℕ, (n / 2 ^ k) % 4 ≠ 2) :
    ∀ k : ℕ, (n / 2 / 2 ^ k) % 4 ≠ 2 := by
  intro k
  simpa only [Nat.div_div_eq_div_mul, ← pow_succ'] using h (k + 1)

theorem power_of_avoids_all (n : ℕ) (h : ∀ k : ℕ, (n / 2 ^ k) % 4 ≠ 2) :
    ∃ m : ℕ, n + 1 = 2 ^ m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · exact ⟨0, by simp [hn]⟩
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨m, hm⟩ := ih (n / 2) (Nat.div_lt_self hnpos (by norm_num))
      (quotient_avoids n h)
    have hlow := h 0
    simp only [pow_zero, Nat.div_one] at hlow
    have hodd : n = 2 * (n / 2) + 1 := by
      cases m with
      | zero => simp only [pow_zero] at hm; omega
      | succ m => rw [pow_succ] at hm; omega
    refine ⟨m + 1, ?_⟩
    calc
      n + 1 = (n / 2 + 1) * 2 := by omega
      _ = 2 ^ m * 2 := by rw [hm]
      _ = 2 ^ (m + 1) := (pow_succ _ _).symm

theorem append_one_avoids (n : ℕ) (h : ∀ k : ℕ, (n / 2 ^ k) % 4 ≠ 2) :
    ∀ k : ℕ, ((2 * n + 1) / 2 ^ k) % 4 ≠ 2 := by
  intro k
  cases k with
  | zero => simp only [pow_zero, Nat.div_one]; omega
  | succ k =>
    have hdiv : (2 * n + 1) / 2 = n := by omega
    have hh := h k
    rw [← hdiv] at hh
    simpa only [Nat.div_div_eq_div_mul, ← pow_succ'] using hh

theorem power_pred_avoids (m : ℕ) :
    ∀ k : ℕ, ((2 ^ m - 1) / 2 ^ k) % 4 ≠ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp : 0 < (2 : ℕ) ^ m := by positivity
    have heq : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
      rw [pow_succ]
      omega
    rw [heq]
    exact append_one_avoids _ ih

theorem avoids_iff_power (n : ℕ) :
    (∀ k ≤ Nat.log 2 (n + 1), (n / 2 ^ k) % 4 ≠ 2) ↔
      ∃ m : ℕ, n + 1 = 2 ^ m := by
  constructor
  · intro h
    exact power_of_avoids_all n (avoids_all_positions n h)
  · rintro ⟨m, hm⟩ k _
    have hn : n = 2 ^ m - 1 := by omega
    rw [hn]
    exact power_pred_avoids m k

end AutomaticDigits

#print axioms AutomaticDigits.avoids_iff_power

namespace AutomaticReindex

theorem series_eq_lacunary :
    (∑' n : ℕ, (if ∀ k : ℕ, k ≤ Nat.log 2 (n + 1) →
        (n / 2 ^ k) % 4 ≠ 2 then (1 : ℝ) else 0) / 2 ^ (n + 1)) =
      ∑' m : ℕ, (1 / 2 : ℝ) ^ (2 ^ m) := by
  classical
  let a : ℕ → ℝ := fun n =>
    (if ∀ k : ℕ, k ≤ Nat.log 2 (n + 1) → (n / 2 ^ k) % 4 ≠ 2
      then 1 else 0) / 2 ^ (n + 1)
  have hinj : Function.Injective (fun m : ℕ => 2 ^ m - 1) := by
    intro m j h
    change 2 ^ m - 1 = 2 ^ j - 1 at h
    have hm : 0 < (2 : ℕ) ^ m := by positivity
    have hj : 0 < (2 : ℕ) ^ j := by positivity
    apply Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))
    change 2 ^ m = 2 ^ j
    omega
  have hsupp : Function.support a ⊆ Set.range (fun m : ℕ => 2 ^ m - 1) := by
    intro n hn
    have havoid : ∀ k : ℕ, k ≤ Nat.log 2 (n + 1) → (n / 2 ^ k) % 4 ≠ 2 := by
      by_contra h
      simp [Function.mem_support, a, h] at hn
    obtain ⟨m, hm⟩ := (AutomaticDigits.avoids_iff_power n).mp havoid
    exact ⟨m, by change 2 ^ m - 1 = n; omega⟩
  have hterm (m : ℕ) : a (2 ^ m - 1) = (1 / 2 : ℝ) ^ (2 ^ m) := by
    have hp : 0 < (2 : ℕ) ^ m := by positivity
    have heq : 2 ^ m - 1 + 1 = 2 ^ m := by omega
    have havoid := (AutomaticDigits.avoids_iff_power (2 ^ m - 1)).mpr ⟨m, heq⟩
    dsimp only [a]
    rw [if_pos havoid, heq]
    simp only [one_div, inv_pow]
  calc
    (∑' n : ℕ, a n) = ∑' m : ℕ, a (2 ^ m - 1) := (hinj.tsum_eq hsupp).symm
    _ = ∑' m : ℕ, (1 / 2 : ℝ) ^ (2 ^ m) := tsum_congr hterm

end AutomaticReindex

#print axioms AutomaticReindex.series_eq_lacunary

open Filter Finset
open scoped Topology

namespace LacunarySeries

theorem irrational_of_positive_scaled_error (x : ℝ) (A : ℕ → ℤ) (q : ℕ → ℕ)
    (hpos : ∀ n, 0 < (q n : ℝ) * x - A n)
    (hlim : Tendsto (fun n => (q n : ℝ) * x - A n) atTop (𝓝 0)) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  have hrden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hcast : (r.den : ℝ) * (r : ℝ) = r.num := by
    rw [Rat.cast_def]
    field_simp
  have ht : Tendsto (fun n => (r.den : ℝ) * ((q n : ℝ) * r - A n))
      atTop (𝓝 0) := by simpa using hlim.const_mul (r.den : ℝ)
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists
  let z : ℤ := (q n : ℤ) * r.num - (r.den : ℤ) * A n
  have hz : (z : ℝ) = (r.den : ℝ) * ((q n : ℝ) * r - A n) := by
    dsimp [z]
    push_cast
    linear_combination -(q n : ℝ) * hcast
  have hzpos : 0 < z := by
    apply (Int.cast_pos (R := ℝ)).mp
    rw [hz]
    exact mul_pos hrden (hpos n)
  have hone : (1 : ℝ) ≤ z := by exact_mod_cast hzpos
  rw [hz] at hone
  exact (not_lt_of_ge hone) hn

noncomputable def term (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (2 ^ n)

theorem term_pos (n : ℕ) : 0 < term n := by unfold term; positivity

theorem summable_term : Summable term := by
  apply Summable.of_nonneg_of_le (fun n => (term_pos n).le) _
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  intro n
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_of_lt Nat.lt_two_pow_self)

theorem power_gap (k i : ℕ) : 2 ^ k + i ≤ 2 ^ (i + k) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.succ_add, pow_succ]
    have hp : 0 < 2 ^ (i + k) := by positivity
    omega

theorem tail_bound (k : ℕ) : (∑' i : ℕ, term (i + k)) ≤ 2 * term k := by
  have ht : Summable (fun i : ℕ => term (i + k)) := (summable_nat_add_iff k).mpr summable_term
  have hg : Summable (fun i : ℕ => term k * (1 / 2 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left _
  calc
    _ ≤ ∑' i : ℕ, term k * (1 / 2 : ℝ) ^ i := by
      apply Summable.tsum_le_tsum _ ht hg
      intro i
      unfold term
      rw [← pow_add]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (power_gap k i)
    _ = 2 * term k := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring

theorem term_tendsto : Tendsto term atTop (𝓝 0) := by
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))

def denominator (k : ℕ) : ℕ := 2 ^ (2 ^ k)

def numerator (k : ℕ) : ℕ := ∑ i ∈ range (k + 1), 2 ^ (2 ^ k - 2 ^ i)

theorem numerator_eq (k : ℕ) : (numerator k : ℝ) =
    (denominator k : ℝ) * ∑ i ∈ range (k + 1), term i := by
  unfold numerator denominator term
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (mem_range.mp hi)
  rw [one_div, inv_pow]
  exact pow_sub₀ (2 : ℝ) (by norm_num) (Nat.pow_le_pow_right (by decide) hik)

theorem scaled_tail (k : ℕ) :
    (denominator k : ℝ) * (∑' i : ℕ, term i) - numerator k =
      (denominator k : ℝ) * ∑' i : ℕ, term (i + (k + 1)) := by
  rw [← summable_term.sum_add_tsum_nat_add (k + 1), numerator_eq]
  ring

theorem scaled_term (k : ℕ) : (denominator k : ℝ) * term (k + 1) = term k := by
  unfold denominator term
  push_cast
  rw [pow_succ, pow_mul, pow_two, one_div, inv_pow]
  have hp : (2 : ℝ) ^ (2 ^ k) ≠ 0 := by positivity
  field_simp

theorem irrational : Irrational (∑' i : ℕ, term i) := by
  apply irrational_of_positive_scaled_error _ (fun k => (numerator k : ℤ)) denominator
  · intro k
    simp only [Int.cast_natCast]
    rw [scaled_tail]
    apply mul_pos (by unfold denominator; positivity)
    apply ((summable_nat_add_iff (k + 1)).mpr summable_term).tsum_pos
      (fun i => (term_pos (i + (k + 1))).le) 0
    exact term_pos _
  · have hb (k : ℕ) : (denominator k : ℝ) * (∑' i : ℕ, term i) - numerator k ≤
        2 * term k := by
      rw [scaled_tail, ← scaled_term k]
      calc
        _ ≤ (denominator k : ℝ) * (2 * term (k + 1)) :=
          mul_le_mul_of_nonneg_left (tail_bound (k + 1)) (Nat.cast_nonneg _)
        _ = _ := by ring
    have hz (k : ℕ) : 0 ≤ (denominator k : ℝ) * (∑' i : ℕ, term i) - numerator k := by
      rw [scaled_tail]
      exact mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg (fun i => (term_pos _).le))
    simpa only [Int.cast_natCast] using squeeze_zero hz hb
      (by simpa using term_tendsto.const_mul 2)

end LacunarySeries

theorem solution :
    Irrational (∑' n : ℕ, (if ∀ k : ℕ, k ≤ Nat.log 2 (n + 1) →
        (n / 2 ^ k) % 4 ≠ 2 then (1 : ℝ) else 0) / 2 ^ (n + 1)) := by
  rw [AutomaticReindex.series_eq_lacunary]
  exact LacunarySeries.irrational

#print axioms LacunarySeries.irrational_of_positive_scaled_error
#print axioms LacunarySeries.irrational
#print axioms solution
