-- Prove2me | solution 1 for chowla_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T04:06:11.463774+00:00
-- url     : https://prove2.me/submissions/0f4f22a9-4244-49f9-a710-efd8aeddc4a5

import Mathlib
import Definitions.Def_OrdinaryTwoPointCorrelations
import Theorems.Thm_OAI_OrdinaryTwoPointCorrelations_liouville_log_saving

/-!
`chowla_conjecture` (bcec3639) from the published
`OAI.OrdinaryTwoPointCorrelations.liouville_log_saving` (9e7e90b6), specialized to
the forms `n` and `n + 1` (`a₁ = a₂ = 1`, `b₁ = 0`, `b₂ = 1`).
-/

open Filter

namespace OAIChowlaBridge

/-- The summand of the published statement. -/
noncomputable def g (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (ArithmeticFunction.cardFactors n) *
    (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (n + 1))

lemma abs_g_le (n : ℕ) : |g n| ≤ 1 := by
  simp [g, abs_mul]

lemma g_zero : g 0 = 1 := by
  simp [g]

lemma liouville_mul_eq_g {n : ℕ} (hn : n ≠ 0) :
    ((ArithmeticFunction.liouville n : ℂ) * (ArithmeticFunction.liouville (n + 1) : ℂ)) =
      ((g n : ℝ) : ℂ) := by
  rw [ArithmeticFunction.liouville_apply hn,
    ArithmeticFunction.liouville_apply (Nat.succ_ne_zero n)]
  simp [g]

lemma sum_Icc_eq (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.liouville n : ℂ) * (ArithmeticFunction.liouville (n + 1) : ℂ)) =
      ((∑ n ∈ Finset.Icc 1 N, g n : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  exact liouville_mul_eq_g (by simp at hn; omega)

lemma sum_range_eq (N : ℕ) :
    ∑ n ∈ Finset.range N, g n = 1 + ∑ n ∈ Finset.Icc 1 N, g n - g N := by
  induction N with
  | zero => simp [g_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    ring

theorem chowla_of_logSaving
    (h : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (ArithmeticFunction.liouville n : ℂ) * (ArithmeticFunction.liouville (n + 1) : ℂ)‖ ≤
        C * X / Real.rpow (Real.log X) c) :
    Tendsto (fun N : ℕ =>
      (1 : ℝ) / N * ∑ n ∈ Finset.range N,
        ((-1 : ℝ) ^ (ArithmeticFunction.cardFactors n) *
         (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (n + 1))))
      atTop (nhds 0) := by
  obtain ⟨c, hc, C, hC, hb⟩ := h
  -- the bound for natural `N ≥ 3`
  have hN : ∀ N : ℕ, 3 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, g n| ≤ C * N / (Real.log N) ^ c := by
    intro N hN3
    have := hb (N : ℝ) (by exact_mod_cast hN3)
    rw [Nat.floor_natCast, sum_Icc_eq, Complex.norm_real, Real.norm_eq_abs] at this
    simpa [Real.rpow_eq_pow] using this
  -- the comparison sequence tends to zero
  have hlog : Tendsto (fun N : ℕ => (Real.log N) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun N : ℕ => ((Real.log N) ^ c)⁻¹) atTop (nhds 0) :=
    hlog.inv_tendsto_atTop
  have hinvN : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun N : ℕ => 2 * ((N : ℝ))⁻¹ + C * ((Real.log N) ^ c)⁻¹)
      atTop (nhds 0) := by
    simpa using (hinvN.const_mul 2).add (hinv.const_mul C)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 3] with N hN3
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsum : |∑ n ∈ Finset.range N, g n| ≤ 2 + C * N / (Real.log N) ^ c := by
    rw [sum_range_eq]
    have h1 := hN N hN3
    have h2 := abs_g_le N
    calc |1 + ∑ n ∈ Finset.Icc 1 N, g n - g N|
        ≤ |(1 : ℝ)| + |∑ n ∈ Finset.Icc 1 N, g n| + |g N| := by
          have := abs_sub (1 + ∑ n ∈ Finset.Icc 1 N, g n) (g N)
          have := abs_add_le (1 : ℝ) (∑ n ∈ Finset.Icc 1 N, g n)
          linarith
      _ ≤ 2 + C * N / (Real.log N) ^ c := by rw [abs_one]; linarith
  have hg : (fun n => (-1 : ℝ) ^ (ArithmeticFunction.cardFactors n) *
      (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (n + 1))) = g := rfl
  rw [hg, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
  calc 1 / (N : ℝ) * |∑ n ∈ Finset.range N, g n|
      ≤ 1 / N * (2 + C * N / (Real.log N) ^ c) := by gcongr
    _ = 2 * ((N : ℝ))⁻¹ + C * ((Real.log N) ^ c)⁻¹ := by
      field_simp

end OAIChowlaBridge

theorem solution :
    Tendsto (fun N : ℕ =>
      (1 : ℝ) / N * ∑ n ∈ Finset.range N,
        ((-1 : ℝ) ^ (ArithmeticFunction.cardFactors n) *
         (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (n + 1))))
      atTop (nhds 0) := by
  apply OAIChowlaBridge.chowla_of_logSaving
  obtain ⟨c, hc, h⟩ := OAI.OrdinaryTwoPointCorrelations.liouville_log_saving
  obtain ⟨C, hC, hb⟩ := h 1 1 0 1 one_pos one_pos (by norm_num)
  refine ⟨c, hc, C, hC, fun X hX => ?_⟩
  have := hb X hX
  simpa [OAI.TwoPointCorrelations.affineSum, OAI.TwoPointCorrelations.liouville] using this
