-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.proposition_5_4_existence_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:23:20.901162+00:00
-- url     : https://prove2.me/submissions/209f9c84-7265-41ee-b893-77a21144bfd6

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate
import Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_4_closed_form
import Theorems.Thm_SmoothAmbEq_Gaussian_proposition_5_4_existence

open MeasureTheory Set

namespace SAEEU

open SmoothAmbEq.Gaussian

lemma zeta_pos (M : Model) {t : ℝ} (ht : 0 ≤ t) : 0 < M.ζ t := by
  unfold Model.ζ
  have : 0 < M.σ ^ 2 + t * M.σ₀ ^ 2 := by have := M.hσ; have := M.hσ₀; positivity
  have := M.hσ; have := M.hσ₀; positivity

/-- `Ψ` is strictly increasing on `[0, 1/(α ∨ 1))`. -/
lemma Psi_strictMonoOn (M : Model) : StrictMonoOn (Ψ M) (Ico 0 (1 / max M.α 1)) := by
  set S : Set ℝ := {y | 0 < 1 - y ∧ 0 < 1 - M.α * y} with hS
  have hψpos : ∀ y ∈ S, 0 < ψ M y := by
    intro y hy
    unfold ψ
    have := hy.1; have := hy.2
    positivity
  have hψc : ContinuousOn (fun y => 1 / ψ M y) S := by
    apply ContinuousOn.div continuousOn_const _ (fun y hy => (hψpos y hy).ne')
    unfold ψ
    apply ContinuousOn.mul
    apply ContinuousOn.mul
    · apply ContinuousOn.rexp
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro y hy; exact hy.1.ne'
    · apply ContinuousOn.rpow_const (by fun_prop)
      intro y hy; exact Or.inl hy.1.ne'
    · apply ContinuousOn.rpow_const (by fun_prop)
      intro y hy; exact Or.inl hy.2.ne'
  have hsub : Ico 0 (1 / max M.α 1) ⊆ S := by
    intro y hy
    have hm : 0 < max M.α 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hy2 : y * max M.α 1 < 1 := by
      have := hy.2; rwa [lt_div_iff₀ hm] at this
    refine ⟨?_, ?_⟩
    · have : y ≤ y * max M.α 1 := le_mul_of_one_le_right hy.1 (le_max_right _ _)
      linarith
    · rcases le_total 0 M.α with h0 | h0
      · have : M.α * y ≤ y * max M.α 1 := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hy.1
        linarith
      · nlinarith [hy.1]
  intro x hx y hy hxy
  have hxyS : uIcc x y ⊆ S := by
    rw [uIcc_of_le hxy.le]
    exact fun z (hz : z ∈ Icc x y) => hsub ⟨hx.1.trans hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  have h0x : uIcc 0 x ⊆ S := by
    rw [uIcc_of_le hx.1]
    exact fun z (hz : z ∈ Icc 0 x) => hsub ⟨hz.1, lt_of_le_of_lt hz.2 hx.2⟩
  have hix : IntervalIntegrable (fun s => 1 / ψ M s) volume 0 x :=
    (hψc.mono h0x).intervalIntegrable
  have hixy : IntervalIntegrable (fun s => 1 / ψ M s) volume x y :=
    (hψc.mono hxyS).intervalIntegrable
  unfold Ψ
  rw [← intervalIntegral.integral_add_adjacent_intervals hix hixy]
  have : 0 < ∫ s in x..y, 1 / ψ M s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hixy
      (fun z hz => by
        have := hψpos z (hxyS (by rw [uIcc_of_le hxy.le]; exact Ioo_subset_Icc_self hz))
        positivity) hxy
  linarith

end SAEEU

open SmoothAmbEq.Gaussian SAEEU

theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : a < M.α) :
    (∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃) ∧
    ∀ m₂ m₃ m₂' m₃' : ℝ → ℝ, SolvesODE516 M m₂ m₃ → SolvesODE516 M m₂' m₃' →
      EqOn m₂ m₂' (Icc 0 M.T) ∧ EqOn m₃ m₃' (Icc 0 M.T) := by
  refine ⟨proposition_5_4_existence M a ha hα, ?_⟩
  intro m₂ m₃ m₂' m₃' h h'
  obtain ⟨A0, A1, A2⟩ := proposition_5_4_closed_form M a ha hα m₂ m₃ h
  obtain ⟨B0, B1, B2⟩ := proposition_5_4_closed_form M a ha hα m₂' m₃' h'
  by_cases h0 : M.α = 0
  · exact ⟨fun t ht => by rw [(A0 h0 t ht).1, (B0 h0 t ht).1],
      fun t ht => by rw [(A0 h0 t ht).2, (B0 h0 t ht).2]⟩
  by_cases h1 : M.α = 1
  · exact ⟨fun t ht => by rw [(A1 h1 t ht).1, (B1 h1 t ht).1],
      fun t ht => by rw [(A1 h1 t ht).2, (B1 h1 t ht).2]⟩
  have hu : ∀ t ∈ Icc 0 M.T, M.ζ t * m₂ t = M.ζ t * m₂' t := by
    intro t ht
    obtain ⟨hA, hAΨ, -⟩ := A2 h0 h1 t ht
    obtain ⟨hB, hBΨ, -⟩ := B2 h0 h1 t ht
    have := (Psi_strictMonoOn M).injOn hA hB (hAΨ.trans hBΨ.symm)
    linarith
  have hm2 : EqOn m₂ m₂' (Icc 0 M.T) := by
    intro t ht
    have := hu t ht
    exact mul_left_cancel₀ (zeta_pos M ht.1).ne' this
  refine ⟨hm2, fun t ht => ?_⟩
  rw [(A2 h0 h1 t ht).2.2, (B2 h0 h1 t ht).2.2, hm2 ht]
