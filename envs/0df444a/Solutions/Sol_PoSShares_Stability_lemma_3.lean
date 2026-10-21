-- Prove2me | solution 1 for PoSShares.Stability.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:16:51.669973+00:00
-- url     : https://prove2.me/submissions/b43b3832-0e46-4e64-8840-2e0e81d85579

import Mathlib
import Definitions.Def_PoSShares_Stability_Model
import Definitions.Def_PoSShares_Stability_VarianceSeq

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology PoSShares.Stability

theorem stab_alpha_step (ν : ℝ) (θ : ℕ → ℝ) (hν : 0 < ν) (hθ : ∀ n : ℕ, 1 ≤ n → 0 ≤ θ n)
    (n : ℕ) :
    (alphaSeq ν θ n ∈ Set.Icc (0 : ℝ) 1) →
      (alphaSeq ν θ n ≤ alphaSeq ν θ (n + 1) ∧ alphaSeq ν θ (n + 1) ∈ Set.Icc (0 : ℝ) 1) := by
  rintro ⟨h0, h1⟩
  have hsum : 0 ≤ ∑ k ∈ Finset.Icc 1 n, θ k :=
    Finset.sum_nonneg (fun k hk => hθ k (Finset.mem_Icc.mp hk).1)
  have hθn : 0 ≤ θ (n + 1) := hθ _ (by omega)
  have hD : ν + ∑ k ∈ Finset.Icc 1 (n + 1), θ k = ν + ∑ k ∈ Finset.Icc 1 n, θ k + θ (n + 1) := by
    rw [Finset.sum_Icc_succ_top (by omega)]; ring
  have hDpos : 0 < ν + ∑ k ∈ Finset.Icc 1 (n + 1), θ k := by rw [hD]; linarith
  set c : ℝ := (θ (n + 1) / (ν + ∑ k ∈ Finset.Icc 1 (n + 1), θ k)) ^ 2 with hc
  have hq0 : 0 ≤ θ (n + 1) / (ν + ∑ k ∈ Finset.Icc 1 (n + 1), θ k) := div_nonneg hθn hDpos.le
  have hq1 : θ (n + 1) / (ν + ∑ k ∈ Finset.Icc 1 (n + 1), θ k) ≤ 1 := by
    rw [div_le_one hDpos, hD]; linarith
  have hc0 : 0 ≤ c := sq_nonneg _
  have hc1 : c ≤ 1 := by rw [hc]; nlinarith
  have hs : alphaSeq ν θ (n + 1) = alphaSeq ν θ n + c * (1 - alphaSeq ν θ n) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]; nlinarith
  · rw [hs]; nlinarith
  · rw [hs]; nlinarith

theorem solution (ν : ℝ) (θ : ℕ → ℝ) (hν : 0 < ν) (hθ : ∀ n : ℕ, 1 ≤ n → 0 ≤ θ n) :
    ∀ n : ℕ, 1 ≤ n →
      alphaSeq ν θ n ∈ Set.Icc (0 : ℝ) 1 ∧ alphaSeq ν θ n ≤ alphaSeq ν θ (n + 1) := by
  have key : ∀ n : ℕ, alphaSeq ν θ n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    induction n with
    | zero => simp [alphaSeq]
    | succ n ih => exact (stab_alpha_step ν θ hν hθ n ih).2
  intro n _
  exact ⟨key n, (stab_alpha_step ν θ hν hθ n (key n)).1⟩
