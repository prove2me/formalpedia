-- Prove2me | solution 1 for TwoFoldOPI.schurFailureSum_le_dist_bound
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T18:55:35.056626+00:00
-- url     : https://prove2.me/submissions/558e7491-9358-467c-b037-e8c0d472241d

import Mathlib
import Definitions.Def_TwoFoldOPI_schurFailureSum
import Definitions.Def_TwoFoldOPI_minDist

open TwoFoldOPI

theorem solution {K : Type*} [Field K] [Fintype K] [DecidableEq K] {M : ℕ}
    (D : Submodule K (Fin M → K)) :
    schurFailureSum D ≤
      (Fintype.card K : ℝ) ^ (Module.finrank K D + Module.finrank K (schurSquare D)) /
        ((Fintype.card K : ℝ) - 1) ^ minDist D := by
  classical
  set q : ℝ := (Fintype.card K : ℝ) with hq
  have hq2 : (2 : ℝ) ≤ q := by
    have := Fintype.one_lt_card (α := K)
    rw [hq]; exact_mod_cast this
  have hq1 : (1 : ℝ) ≤ q - 1 := by linarith
  have hq0 : (0 : ℝ) < q - 1 := by linarith
  set a := Module.finrank K D
  set b := Module.finrank K (schurSquare D)
  set d := minDist D
  set S := Finset.univ.filter (fun c : Fin M → K => c ∈ D ∧ c ≠ 0) with hS
  -- each term is bounded by `q^b / (q-1)^d`
  have hterm : ∀ c ∈ S,
      q ^ Module.finrank K (shorten (schurSquare D) (zeroSet c)) / (q - 1) ^ hammingNorm c ≤
        q ^ b / (q - 1) ^ d := by
    intro c hc
    rw [hS, Finset.mem_filter] at hc
    obtain ⟨-, hcD, hc0⟩ := hc
    have hdim : Module.finrank K (shorten (schurSquare D) (zeroSet c)) ≤ b := by
      apply Submodule.finrank_mono
      intro x hx
      exact hx.1
    have hwt : d ≤ hammingNorm c := by
      apply Nat.sInf_le
      exact ⟨c, hcD, hc0, rfl⟩
    have hnum : q ^ Module.finrank K (shorten (schurSquare D) (zeroSet c)) ≤ q ^ b :=
      pow_le_pow_right₀ (by linarith) hdim
    have hden : (q - 1) ^ d ≤ (q - 1) ^ hammingNorm c := pow_le_pow_right₀ hq1 hwt
    have hdpos : 0 < (q - 1) ^ d := pow_pos hq0 _
    calc q ^ Module.finrank K (shorten (schurSquare D) (zeroSet c)) / (q - 1) ^ hammingNorm c
        ≤ q ^ b / (q - 1) ^ hammingNorm c := by
          gcongr
      _ ≤ q ^ b / (q - 1) ^ d := by
          apply div_le_div_of_nonneg_left (by positivity) hdpos hden
  -- the number of terms is at most `|D| = q^a`
  have hcard : (S.card : ℝ) ≤ q ^ a := by
    have h1 : S.card ≤ (Finset.univ.filter (fun c : Fin M → K => c ∈ D)).card := by
      apply Finset.card_le_card
      intro c hc
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.1
    have h2 : (Finset.univ.filter (fun c : Fin M → K => c ∈ D)).card = Fintype.card D := by
      rw [Fintype.card_subtype]
    have h3 : Fintype.card D = Fintype.card K ^ a := Module.card_eq_pow_finrank
    have : S.card ≤ Fintype.card K ^ a := by omega
    rw [hq]; exact_mod_cast this
  have hsum : schurFailureSum D = ∑ c ∈ S,
      q ^ Module.finrank K (shorten (schurSquare D) (zeroSet c)) / (q - 1) ^ hammingNorm c := by
    unfold schurFailureSum
    rw [hS, hq]
  rw [hsum]
  calc ∑ c ∈ S,
        q ^ Module.finrank K (shorten (schurSquare D) (zeroSet c)) / (q - 1) ^ hammingNorm c
      ≤ ∑ _c ∈ S, q ^ b / (q - 1) ^ d := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (q ^ b / (q - 1) ^ d) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ q ^ a * (q ^ b / (q - 1) ^ d) := by
        gcongr
    _ = q ^ (a + b) / (q - 1) ^ d := by rw [pow_add, mul_div_assoc]
