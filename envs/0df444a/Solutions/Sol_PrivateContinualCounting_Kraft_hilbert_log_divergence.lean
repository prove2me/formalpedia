-- Prove2me | solution 1 for PrivateContinualCounting.Kraft.hilbert_log_divergence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:44:58.0762+00:00
-- url     : https://prove2.me/submissions/2293bd30-ca14-4643-aab5-ef6f2224484d

import Theorems.Thm_PrivateContinualCounting_Kraft_hilbert_inequality

set_option autoImplicit false

open Finset Filter Topology

namespace PCCKraftCore

/-- The Hilbert transform `χ_j = Σ_k β_k/(j+k+1)`. -/
noncomputable def chi (β : ℕ → ℝ) (j : ℕ) : ℝ := ∑' k, β k / ((j:ℝ) + k + 1)

lemma chi_summable (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (j : ℕ) : Summable (fun k => β k / ((j:ℝ) + k + 1)) :=
  (PrivateContinualCounting.Kraft.hilbert_inequality β hβ hβ2).1 j

lemma chi_nonneg (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (j : ℕ) : 0 ≤ chi β j :=
  tsum_nonneg (fun k => by have := hβ k; positivity)

lemma sum_le_chi (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (j N : ℕ) : ∑ k ∈ range N, β k / ((j:ℝ) + k + 1) ≤ chi β j :=
  (chi_summable β hβ hβ2 j).sum_le_tsum _ (fun k _ => by have := hβ k; positivity)

lemma chi_sq_summable (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2)) :
    Summable (fun j => chi β j ^ 2) :=
  (PrivateContinualCounting.Kraft.hilbert_inequality β hβ hβ2).2.1

lemma chi_sq_sum_le (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (n : ℕ) : ∑ j ∈ range n, chi β j ^ 2 ≤ 16 * ∑' k, β k ^ 2 :=
  ((chi_sq_summable β hβ hβ2).sum_le_tsum _ (fun j _ => sq_nonneg _)).trans
    (PrivateContinualCounting.Kraft.hilbert_inequality β hβ hβ2).2.2

/-- Weighting the convolution identities by `1/(m+1)`. -/
lemma log_le_sum_chi (α β : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2))
    (hid : ∀ m, 1 ≤ ∑ j ∈ range (m + 1), α j * β (m - j)) (n : ℕ) :
    Real.log ((n:ℝ) + 1) ≤ ∑ j ∈ range n, α j * chi β j := by
  have h1 : Real.log ((n:ℝ) + 1) ≤ ∑ m ∈ range n, 1 / ((m:ℝ) + 1) := by
    have := log_add_one_le_harmonic n
    simpa [harmonic] using this
  refine h1.trans ?_
  set f : ℕ → ℕ → ℝ := fun j k => α j * β k / (((j + k : ℕ) : ℝ) + 1) with hf
  have h2 : ∀ m : ℕ, 1 / ((m:ℝ) + 1) ≤ ∑ j ∈ range (m + 1), f j (m - j) := by
    intro m
    have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have : ∑ j ∈ range (m + 1), f j (m - j) =
        (∑ j ∈ range (m + 1), α j * β (m - j)) / ((m:ℝ) + 1) := by
      rw [sum_div]
      apply sum_congr rfl
      intro j hj
      have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
      simp only [hf, Nat.add_sub_cancel' hj']
    rw [this]
    exact div_le_div_of_nonneg_right (hid m) hm.le
  calc ∑ m ∈ range n, 1 / ((m:ℝ) + 1) ≤ ∑ m ∈ range n, ∑ j ∈ range (m + 1), f j (m - j) :=
        sum_le_sum (fun m _ => h2 m)
    _ = ∑ j ∈ range n, ∑ k ∈ range (n - j), f j k := sum_range_diag_flip n f
    _ ≤ ∑ j ∈ range n, α j * chi β j := by
        apply sum_le_sum
        intro j _
        have : ∑ k ∈ range (n - j), f j k = α j * ∑ k ∈ range (n - j), β k / ((j:ℝ) + k + 1) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro k _
          simp only [hf]
          push_cast
          ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (sum_le_chi β hβ hβ2 j _) (hα j)


lemma sum_Ico_chi_sq_le (β : ℕ → ℝ) (hβ : ∀ k, 0 ≤ β k) (hβ2 : Summable (fun k => β k ^ 2))
    (J n : ℕ) : ∑ j ∈ Ico J n, chi β j ^ 2 ≤ ∑' i, chi β (i + J) ^ 2 := by
  rw [sum_Ico_eq_sum_range]
  have hs : Summable (fun i => chi β (i + J) ^ 2) :=
    (summable_nat_add_iff J).mpr (chi_sq_summable β hβ hβ2)
  calc ∑ k ∈ range (n - J), chi β (J + k) ^ 2 = ∑ k ∈ range (n - J), chi β (k + J) ^ 2 := by
        simp_rw [add_comm J]
    _ ≤ _ := hs.sum_le_tsum _ (fun i _ => sq_nonneg _)


/-- Abstract form of Theorem 3.1. -/
theorem core_divergence (α β : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2))
    (hid : ∀ m, 1 ≤ ∑ j ∈ range (m + 1), α j * β (m - j)) :
    Tendsto (fun n : ℕ => (∑ j ∈ range n, α j ^ 2) / (Real.log n) ^ 2) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hT := tendsto_sum_nat_add (fun j => chi β j ^ 2)
  have hev : ∀ᶠ J in atTop, ∑' i, chi β (i + J) ^ 2 < 1 / (4 * M') :=
    hT.eventually (gt_mem_nhds (by positivity))
  obtain ⟨J, hJ⟩ := hev.exists
  set T := ∑' i, chi β (i + J) ^ 2 with hTdef
  have hT0 : 0 ≤ T := tsum_nonneg (fun i => sq_nonneg _)
  set A := ∑ j ∈ range J, α j * chi β j with hA
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max (2 * A) 1)
  filter_upwards [hlog, eventually_ge_atTop J] with n hn hnJ
  simp only [Function.comp] at hn
  set L := Real.log (n:ℝ) with hL
  set E := ∑ j ∈ range n, α j ^ 2 with hE
  have hE0 : 0 ≤ E := sum_nonneg (fun j _ => sq_nonneg _)
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hn
  have hLA : 2 * A ≤ L := le_trans (le_max_left _ _) hn
  set S := ∑ j ∈ Ico J n, α j * chi β j with hS
  have hS0 : 0 ≤ S := sum_nonneg (fun j _ => mul_nonneg (hα j) (chi_nonneg β hβ j))
  have hsplit : ∑ j ∈ range n, α j * chi β j = A + S := (sum_range_add_sum_Ico _ hnJ).symm
  have hlogle : L ≤ A + S := by
    have h1 := log_le_sum_chi α β hα hβ hβ2 hid n
    have h2 : L ≤ Real.log ((n:ℝ) + 1) := by
      have hnpos : (0:ℝ) < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hL; linarith
        · exact_mod_cast h
      exact Real.log_le_log hnpos (by linarith)
    linarith
  have hSsq : S ^ 2 ≤ E * T := by
    have hcs := sum_mul_sq_le_sq_mul_sq (Ico J n) α (chi β)
    have h1 : ∑ j ∈ Ico J n, α j ^ 2 ≤ E := by
      rw [hE, ← sum_range_add_sum_Ico _ hnJ]
      have : 0 ≤ ∑ j ∈ range J, α j ^ 2 := sum_nonneg (fun j _ => sq_nonneg _)
      linarith
    have h2 : ∑ j ∈ Ico J n, chi β j ^ 2 ≤ T := sum_Ico_chi_sq_le β hβ hβ2 J n
    calc S ^ 2 ≤ (∑ j ∈ Ico J n, α j ^ 2) * ∑ j ∈ Ico J n, chi β j ^ 2 := hcs
      _ ≤ E * T := by
        apply mul_le_mul h1 h2 (sum_nonneg (fun j _ => sq_nonneg _)) hE0
  have hS2 : L / 2 ≤ S := by linarith
  have hL2 : L ^ 2 / 4 ≤ E * T := by
    have : (L / 2) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (by linarith) hS2 2
    nlinarith
  have hET : E * T ≤ E / (4 * M') := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hJ.le hE0
    calc E * T * (4 * M') = (E * T) * (4 * M') := rfl
      _ ≤ (E * (1 / (4 * M'))) * (4 * M') := by gcongr
      _ = E := by field_simp
  have hLpos : 0 < L ^ 2 := by positivity
  rw [le_div_iff₀ hLpos]
  have : M' * L ^ 2 ≤ E := by
    have := hL2.trans hET
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  calc M * L ^ 2 ≤ M' * L ^ 2 := by gcongr; exact le_max_left _ _
    _ ≤ E := this


end PCCKraftCore

theorem solution (α β : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2))
    (hconv : ∀ m : ℕ, 1 ≤ ∑ j ∈ Finset.range (m + 1), α j * β (m - j)) :
    Filter.Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, α j ^ 2) / (Real.log (n : ℝ)) ^ 2)
      Filter.atTop Filter.atTop :=
  PCCKraftCore.core_divergence α β hα hβ hβ2 hconv
