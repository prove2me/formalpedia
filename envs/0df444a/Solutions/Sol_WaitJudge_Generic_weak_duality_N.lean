-- Prove2me | solution 1 for WaitJudge.Generic.weak_duality_N
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:58:11.601957+00:00
-- url     : https://prove2.me/submissions/c0ecde60-164e-41d3-851e-5bbf8dbad34f

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting

set_option autoImplicit false
open MeasureTheory WaitJudge.Generic

lemma mm_wd_k (N : ℕ) (ε : ℕ → ℝ) (hε : ∀ k ≤ N, 0 ≤ ε k ∧ ε k ≤ 1)
    (μ : ℕ → Measure ℝ) (hfinite : ∀ k ≤ N, μ k Set.univ < ⊤)
    (lam : ℕ → ℝ) (hdual : IsFeasibleDualN N ε lam) (k : ℕ) (hk : k ≤ N) :
    (N.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k) ≤
      ∑ m ∈ Finset.Icc k N, lam m * ((m.choose k : ℝ) *
        ∫ v in Set.Icc (0 : ℝ) 1, (1 - v) ^ (m - k) ∂(μ k)) := by
  haveI : IsFiniteMeasure (μ k) := ⟨hfinite k hk⟩
  have hcont : ∀ j : ℕ, IntegrableOn (fun v : ℝ => (1 - v) ^ j) (Set.Icc (0 : ℝ) 1) (μ k) := by
    intro j
    exact (by fun_prop : Continuous (fun v : ℝ => (1 - v) ^ j)).integrableOn_Icc
  have h1 : ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k) =
      ∫ v in Set.Icc (0 : ℝ) 1, (Set.Ioc (ε k) 1).indicator (fun v => (1 - v) ^ (N - k)) v ∂(μ k) := by
    have hset : Set.Icc (0 : ℝ) 1 ∩ Set.Ioc (ε k) 1 = Set.Ioc (ε k) 1 := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith [(hε k hk).1], h2⟩, h1, h2⟩
    rw [setIntegral_indicator measurableSet_Ioc, hset]
  rw [h1, ← integral_const_mul]
  have h2 : ∑ m ∈ Finset.Icc k N, lam m * ((m.choose k : ℝ) *
        ∫ v in Set.Icc (0 : ℝ) 1, (1 - v) ^ (m - k) ∂(μ k)) =
      ∫ v in Set.Icc (0 : ℝ) 1, ∑ m ∈ Finset.Icc k N, lam m * ((m.choose k : ℝ) * (1 - v) ^ (m - k)) ∂(μ k) := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [integral_const_mul, integral_const_mul]
    · intro m _
      exact ((hcont _).const_mul _).const_mul _
  rw [h2]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Icc (fun v hv => ?_)
  · exact (((hcont _).indicator measurableSet_Ioc).const_mul _ : _)
  · exact integrable_finsetSum _ (fun m _ => ((hcont _).const_mul _).const_mul _)
  · have := hdual k hk (1 - v) ⟨by linarith [hv.2], by linarith [hv.1]⟩
    by_cases hvm : v ∈ Set.Ioc (ε k) 1
    · have hmem : (1 - v) ∈ Set.Ico 0 (1 - ε k) := ⟨by linarith [hvm.2], by linarith [hvm.1]⟩
      rw [Set.indicator_of_mem hmem, mul_one] at this
      rw [Set.indicator_of_mem hvm]
      refine this.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    · have hmem : (1 - v) ∉ Set.Ico 0 (1 - ε k) := by
        intro h; exact hvm ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [Set.indicator_of_notMem hmem, mul_zero] at this
      rw [Set.indicator_of_notMem hvm, mul_zero]
      refine this.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring

theorem solution
    (N : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ k ≤ N, 0 ≤ ε k ∧ ε k ≤ 1)
    (μ : ℕ → Measure ℝ)
    (hfinite : ∀ k ≤ N, μ k Set.univ < ⊤)
    (hmoment : ∀ m ≤ N,
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) *
        ∫ v in Set.Icc (0 : ℝ) 1, (1 - v) ^ (m - k) ∂(μ k) = 1)
    (lam : ℕ → ℝ) (hdual : IsFeasibleDualN N ε lam) :
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k) ≤
    ∑ m ∈ Finset.range (N + 1), lam m := by
  calc ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k)
      ≤ ∑ k ∈ Finset.range (N + 1), ∑ m ∈ Finset.Icc k N, lam m * ((m.choose k : ℝ) *
        ∫ v in Set.Icc (0 : ℝ) 1, (1 - v) ^ (m - k) ∂(μ k)) :=
        Finset.sum_le_sum (fun k hk => mm_wd_k N ε hε μ hfinite lam hdual k
          (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
    _ = ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1), lam m * ((m.choose k : ℝ) *
        ∫ v in Set.Icc (0 : ℝ) 1, (1 - v) ^ (m - k) ∂(μ k)) := by
        refine Finset.sum_comm' (fun k m => ?_)
        simp only [Finset.mem_range, Finset.mem_Icc]
        omega
    _ = ∑ m ∈ Finset.range (N + 1), lam m := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [← Finset.mul_sum, hmoment m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)), mul_one]
