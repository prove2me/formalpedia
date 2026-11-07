-- Prove2me | solution 1 for ResolvingNRM.IRT.irt_regret_uniformly_bounded
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:56:20.630339+00:00
-- url     : https://prove2.me/submissions/1d3052ea-4e66-4ae1-a812-ac7bc04806b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model
import Theorems.Thm_ResolvingNRM_IRT_regret_decomposition
import Theorems.Thm_ResolvingNRM_IRT_schedule_sum_bounded

open RLPBidPrice.Unbiased Matrix ResolvingNRM.IRT

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℕ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C →
        hindsightValue A r lam (T : ℝ) C - irtValue A r lam sel (Kirt T) (T : ℝ) C ≤ M := by
  obtain ⟨κ, hκ, M, hM⟩ := regret_decomposition A r lam hlam hr hA
  obtain ⟨B, hB⟩ := schedule_sum_bounded κ hκ
  refine ⟨|M| * B, fun sel hsel T hT C hC => ?_⟩
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have h1 := hM sel hsel (T : ℝ) hT' C hC (Kirt (T : ℝ))
  have h2 := hB (T : ℝ) hT'
  set S := ∑ u ∈ Finset.range (Kirt (T : ℝ)),
      (T : ℝ) ^ ((5 / 6 : ℝ) ^ u) * Real.exp (-κ * (T : ℝ) ^ ((5 / 6 : ℝ) ^ u / 6)) with hS
  set X := (T : ℝ) ^ ((5 / 6 : ℝ) ^ Kirt (T : ℝ) / 2) with hX
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun u _ =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hX0 : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  have h3 : M * S + M * X ≤ |M| * B := by
    rw [← mul_add]
    calc M * (S + X) ≤ |M| * (S + X) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (by linarith)
      _ ≤ |M| * B := mul_le_mul_of_nonneg_left h2 (abs_nonneg M)
  linarith
