-- Prove2me | solution 1 for PrivateContinualCounting.Kraft.hilbert_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:44:56.420809+00:00
-- url     : https://prove2.me/submissions/5b842c7d-4474-4059-835d-7514f7071ae4

import Mathlib

set_option autoImplicit false

open Finset Filter Topology

namespace PCCKraftCore

lemma sum_inv_sqrt_le (n : ℕ) : ∑ k ∈ range n, 1 / Real.sqrt ((k:ℝ) + 1) ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 : 1 / Real.sqrt ((n:ℝ) + 1) ≤ 2 * (Real.sqrt ((n:ℝ)+1) - Real.sqrt n) := by
      have hs : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
      have hsn : Real.sqrt n ≤ Real.sqrt ((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
      have hsq : Real.sqrt ((n:ℝ)+1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
      have hsq' : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (Real.sqrt ((n:ℝ)+1) - Real.sqrt n), Real.sqrt_nonneg (n:ℝ)]
    push_cast
    linarith

lemma tele_step (k : ℕ) (hk : 1 ≤ k) :
    1 / (((k:ℝ) + 1) * Real.sqrt ((k:ℝ) + 1)) ≤
      2 * (1 / Real.sqrt (k:ℝ) - 1 / Real.sqrt ((k:ℝ) + 1)) := by
  set a := Real.sqrt ((k:ℝ) + 1) with ha
  set b := Real.sqrt (k:ℝ) with hb
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hb0 : 0 < b := Real.sqrt_pos.2 (by linarith)
  have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hsq : a ^ 2 = k + 1 := Real.sq_sqrt (by positivity)
  have hsq' : b ^ 2 = k := Real.sq_sqrt (by positivity)
  have e1 : ((k:ℝ) + 1) * a = a ^ 3 := by rw [← hsq]; ring
  rw [e1]
  have hab : (a - b) * (a + b) = 1 := by nlinarith
  have e2 : 2 * (1 / b - 1 / a) = 2 / ((a + b) * a * b) := by
    field_simp
    exact hab
  rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos ha0 hb0, mul_pos (mul_pos ha0 ha0) hb0]

lemma tail_sum_le (m d : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Ico m (m + d), 1 / (((k:ℝ) + 1) * Real.sqrt ((k:ℝ) + 1)) ≤
      2 * (1 / Real.sqrt (m:ℝ) - 1 / Real.sqrt ((m:ℝ) + d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, sum_Ico_succ_top (by omega)]
    have := tele_step (m + d) (by omega)
    push_cast at this ⊢
    have e : (m:ℝ) + ((d:ℝ) + 1) = m + d + 1 := by ring
    rw [e]
    linarith

lemma tail_sum_le' (j n : ℕ) :
    ∑ k ∈ Ico (j + 1) n, 1 / (((k:ℝ) + 1) * Real.sqrt ((k:ℝ) + 1)) ≤
      2 / Real.sqrt ((j:ℝ) + 1) := by
  rcases le_or_gt n (j + 1) with h | h
  · rw [Ico_eq_empty_of_le h]; simp; positivity
  · obtain ⟨d, rfl⟩ : ∃ d, n = (j + 1) + d := ⟨n - (j + 1), by omega⟩
    have := tail_sum_le (j + 1) d (by omega)
    push_cast at this ⊢
    have h2 : 0 ≤ 1 / Real.sqrt ((j:ℝ) + 1 + d) := by positivity
    have e : 2 * (1 / Real.sqrt ((j:ℝ) + 1)) = 2 / Real.sqrt ((j:ℝ) + 1) := by ring
    linarith

/-- Schur row bound for the Hilbert matrix with the weight `1/√(k+1)`. -/
lemma schur_row (j n : ℕ) :
    ∑ k ∈ range n, 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1)) ≤
      4 / Real.sqrt ((j:ℝ) + 1) := by
  have hpos : ∀ k : ℕ, 0 ≤ 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1)) := fun k => by positivity
  calc ∑ k ∈ range n, 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1))
      ≤ ∑ k ∈ range (max n (j + 1)), 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1)) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (le_max_left _ _))
          (fun k _ _ => hpos k)
    _ = ∑ k ∈ range (j + 1), 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1)) +
        ∑ k ∈ Ico (j + 1) (max n (j + 1)), 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1)) :=
        (sum_range_add_sum_Ico _ (le_max_right _ _)).symm
    _ ≤ 2 / Real.sqrt ((j:ℝ) + 1) + 2 / Real.sqrt ((j:ℝ) + 1) := by
        gcongr ?_ + ?_
        · calc ∑ k ∈ range (j + 1), 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1))
              ≤ ∑ k ∈ range (j + 1), (1 / ((j:ℝ) + 1)) * (1 / Real.sqrt ((k:ℝ) + 1)) := by
                apply sum_le_sum
                intro k _
                rw [one_div_mul_one_div]
                apply one_div_le_one_div_of_le (by positivity)
                gcongr
                linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
            _ = (1 / ((j:ℝ) + 1)) * ∑ k ∈ range (j + 1), 1 / Real.sqrt ((k:ℝ) + 1) := by
                rw [mul_sum]
            _ ≤ (1 / ((j:ℝ) + 1)) * (2 * Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
                gcongr; exact sum_inv_sqrt_le (j + 1)
            _ = 2 / Real.sqrt ((j:ℝ) + 1) := by
                have hs : 0 < Real.sqrt ((j:ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
                have hsq : Real.sqrt ((j:ℝ) + 1) ^ 2 = (j:ℝ) + 1 := Real.sq_sqrt (by positivity)
                push_cast
                calc (1 / ((j:ℝ) + 1)) * (2 * Real.sqrt ((j:ℝ) + 1))
                    = 2 * Real.sqrt ((j:ℝ) + 1) / (Real.sqrt ((j:ℝ) + 1) * Real.sqrt ((j:ℝ) + 1)) := by
                      rw [← sq, hsq]; ring
                  _ = 2 / Real.sqrt ((j:ℝ) + 1) := by field_simp
        · calc ∑ k ∈ Ico (j + 1) (max n (j + 1)), 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1))
              ≤ ∑ k ∈ Ico (j + 1) (max n (j + 1)), 1 / (((k:ℝ) + 1) * Real.sqrt ((k:ℝ) + 1)) := by
                apply sum_le_sum
                intro k _
                apply one_div_le_one_div_of_le (by positivity)
                gcongr
                linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
            _ ≤ 2 / Real.sqrt ((j:ℝ) + 1) := tail_sum_le' j _
    _ = 4 / Real.sqrt ((j:ℝ) + 1) := by ring

/-- Finite Hilbert inequality (Schur test), constant 16. -/
lemma hilbert_finite (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (n N : ℕ) :
    ∑ j ∈ range n, (∑ k ∈ range N, β k / ((j:ℝ) + k + 1)) ^ 2 ≤
      16 * ∑ k ∈ range N, β k ^ 2 := by
  have hrow : ∀ j : ℕ, (∑ k ∈ range N, β k / ((j:ℝ) + k + 1)) ^ 2 ≤
      (4 / Real.sqrt ((j:ℝ) + 1)) *
        ∑ k ∈ range N, β k ^ 2 * Real.sqrt ((k:ℝ) + 1) / ((j:ℝ) + k + 1) := by
    intro j
    have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (range N)
      (r := fun k => β k / ((j:ℝ) + k + 1))
      (f := fun k => 1 / (((j:ℝ) + k + 1) * Real.sqrt ((k:ℝ) + 1)))
      (g := fun k => β k ^ 2 * Real.sqrt ((k:ℝ) + 1) / ((j:ℝ) + k + 1))
      (fun k _ => by positivity) (fun k _ => by positivity) (by
        intro k _
        have hs : 0 < Real.sqrt ((k:ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
        have hjk : (0:ℝ) < (j:ℝ) + k + 1 := by positivity
        apply le_of_eq
        field_simp)
    refine h.trans ?_
    gcongr
    exact schur_row j N
  calc ∑ j ∈ range n, (∑ k ∈ range N, β k / ((j:ℝ) + k + 1)) ^ 2
      ≤ ∑ j ∈ range n, (4 / Real.sqrt ((j:ℝ) + 1)) *
          ∑ k ∈ range N, β k ^ 2 * Real.sqrt ((k:ℝ) + 1) / ((j:ℝ) + k + 1) :=
        sum_le_sum (fun j _ => hrow j)
    _ = 4 * ∑ k ∈ range N, β k ^ 2 * Real.sqrt ((k:ℝ) + 1) *
          ∑ j ∈ range n, 1 / (((k:ℝ) + j + 1) * Real.sqrt ((j:ℝ) + 1)) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro k _
        apply sum_congr rfl; intro j _
        have hs : 0 < Real.sqrt ((j:ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
        have hjk : (0:ℝ) < (j:ℝ) + k + 1 := by positivity
        field_simp
        ring
    _ ≤ 4 * ∑ k ∈ range N, β k ^ 2 * Real.sqrt ((k:ℝ) + 1) * (4 / Real.sqrt ((k:ℝ) + 1)) := by
        gcongr with k _
        exact schur_row k n
    _ = 16 * ∑ k ∈ range N, β k ^ 2 := by
        rw [mul_sum, mul_sum]
        apply sum_congr rfl; intro k _
        have hs : 0 < Real.sqrt ((k:ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
        field_simp
        ring


/-- The Hilbert transform `χ_j = Σ_k β_k/(j+k+1)`. -/
noncomputable def chi (β : ℕ → ℝ) (j : ℕ) : ℝ := ∑' k, β k / ((j:ℝ) + k + 1)

lemma summable_inv_sq_succ : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using h

lemma chi_summable (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (j : ℕ) : Summable (fun k => β k / ((j:ℝ) + k + 1)) := by
  refine Summable.of_nonneg_of_le (fun k => by have := hβ k; positivity) (fun k => ?_)
    (hβ2.add summable_inv_sq_succ)
  have hx : (0:ℝ) < (j:ℝ) + k + 1 := by positivity
  have hy : 1 / ((j:ℝ) + k + 1) ≤ 1 / ((k:ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
  have hy0 : 0 ≤ 1 / ((j:ℝ) + k + 1) := by positivity
  have hyy : (1 / ((j:ℝ) + k + 1)) ^ 2 ≤ 1 / ((k:ℝ) + 1) ^ 2 := by
    rw [← one_div_pow]; gcongr
  have : β k / ((j:ℝ) + k + 1) = β k * (1 / ((j:ℝ) + k + 1)) := by ring
  rw [this]
  nlinarith [sq_nonneg (β k - 1 / ((j:ℝ) + k + 1)), hβ k]

lemma chi_nonneg (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (j : ℕ) : 0 ≤ chi β j :=
  tsum_nonneg (fun k => by have := hβ k; positivity)

lemma sum_le_chi (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (j N : ℕ) : ∑ k ∈ range N, β k / ((j:ℝ) + k + 1) ≤ chi β j :=
  (chi_summable β hβ hβ2 j).sum_le_tsum _ (fun k _ => by have := hβ k; positivity)

lemma chi_sq_sum_le (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (n : ℕ) : ∑ j ∈ range n, chi β j ^ 2 ≤ 16 * ∑' k, β k ^ 2 := by
  have ht : Tendsto (fun N => ∑ j ∈ range n, (∑ k ∈ range N, β k / ((j:ℝ) + k + 1)) ^ 2)
      atTop (𝓝 (∑ j ∈ range n, chi β j ^ 2)) := by
    apply tendsto_finsetSum
    intro j _
    exact ((chi_summable β hβ hβ2 j).hasSum.tendsto_sum_nat).pow 2
  refine le_of_tendsto' ht (fun N => (hilbert_finite β hβ n N).trans ?_)
  gcongr
  exact hβ2.sum_le_tsum _ (fun k _ => sq_nonneg _)

lemma chi_sq_summable (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2)) :
    Summable (fun j => chi β j ^ 2) :=
  summable_of_sum_range_le (fun j => sq_nonneg _) (chi_sq_sum_le β hβ hβ2)


end PCCKraftCore

theorem solution (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2)) :
    (∀ j : ℕ, Summable (fun k : ℕ => β k / ((j : ℝ) + k + 1))) ∧
    Summable (fun j : ℕ => (∑' k : ℕ, β k / ((j : ℝ) + k + 1)) ^ 2) ∧
    ∑' j : ℕ, (∑' k : ℕ, β k / ((j : ℝ) + k + 1)) ^ 2 ≤ 16 * ∑' k : ℕ, β k ^ 2 := by
  refine ⟨PCCKraftCore.chi_summable β hβ hβ2, PCCKraftCore.chi_sq_summable β hβ hβ2, ?_⟩
  exact Real.tsum_le_of_sum_range_le (fun j => sq_nonneg _) (PCCKraftCore.chi_sq_sum_le β hβ hβ2)
