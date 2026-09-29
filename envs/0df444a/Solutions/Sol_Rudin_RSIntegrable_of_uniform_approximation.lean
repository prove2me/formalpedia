-- Prove2me | solution 1 for Rudin.RSIntegrable_of_uniform_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T00:57:42.937345+00:00
-- url     : https://prove2.me/submissions/494fe25f-90e6-491f-a602-e16863ace765

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_integrals_stable

open Rudin

theorem solution {a b : ℝ} (hab : a ≤ b)
    (α : ℝ → ℝ) (hα : MonotoneOn α (Set.Icc a b))
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hint : ∀ n, RSIntegrable a b (f n) α)
    (happrox : ∀ ε > 0, ∃ n, ∀ x ∈ Set.Icc a b, |f n x - g x| ≤ ε) :
    RSIntegrable a b g α := by
  have hspan : 0 ≤ α b - α a := by
    exact sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  unfold RSIntegrable
  apply eq_of_abs_sub_le_all
  intro δ hδ
  let Δ : ℝ := α b - α a
  let ε : ℝ := δ / (2 * (Δ + 1))
  have hΔ : 0 ≤ Δ := hspan
  have hden : 0 < 2 * (Δ + 1) := by positivity
  have hε : 0 < ε := div_pos hδ hden
  obtain ⟨n, hn⟩ := happrox ε hε
  have hs := Rudin.integrals_stable hab α g (f n) hα hε.le (by
    intro x hx
    simpa [abs_sub_comm] using hn x hx)
  have hu := hs.1
  have hl := (Rudin.integrals_stable hab α (f n) g hα hε.le hn).2
  have hratio : ε * Δ + ε * Δ ≤ δ := by
    calc
      ε * Δ + ε * Δ = δ * (Δ / (Δ + 1)) := by
        dsimp [ε]
        field_simp [ne_of_gt (show 0 < Δ + 1 by positivity)]
        <;> ring
      _ ≤ δ * 1 := by
        apply mul_le_mul_of_nonneg_left _ hδ.le
        exact (div_le_one (show 0 < Δ + 1 by positivity)).2 (by linarith)
      _ = δ := mul_one δ
  calc
    |upperIntegral a b g α - lowerIntegral a b g α| ≤
        |upperIntegral a b g α - upperIntegral a b (f n) α| +
          |upperIntegral a b (f n) α - lowerIntegral a b g α| :=
      abs_sub_le _ _ _
    _ = |upperIntegral a b g α - upperIntegral a b (f n) α| +
          |lowerIntegral a b (f n) α - lowerIntegral a b g α| := by
      rw [hint n]
    _ ≤ ε * Δ + ε * Δ := add_le_add hu hl
    _ ≤ δ := hratio
