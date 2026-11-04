-- Prove2me | solution 1 for PreAwardInvest.WinWin.top_type_zero_profit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T11:36:17.23901+00:00
-- url     : https://prove2.me/submissions/eb1d0720-1af8-4b62-9fbe-8d8770dbeb53

import Mathlib
import Definitions.Def_PreAwardInvest_WinWin_Model

open PreAwardInvest.WinWin
open MeasureTheory

theorem solution {N : ℕ} [NeZero N] (P : Params N) (hS : P.Standing)
    (hsym : ExAnteSymmetric P) (τ : ℝ)
    (βI βA : Fin N → ℝ → ℝ) :
    (IsEqBIA P τ βI → ∀ i, profitBIA P τ βI i (βI i (cHiI P i)) (cHiI P i) = 0) ∧
      (IsEqBAI P βA → ∀ i, profitBAI P βA i (βA i (cHiI P i)) (cHiI P i) = 0) := by
  have hlast := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, hdc, hc, -⟩ := hS
  have hmem : ∀ i, cHiI P i ∈ Set.Icc (cLoI P i) (cHiI P i) := fun i =>
    ⟨by unfold cLoI cHiI; linarith, le_rfl⟩
  have hbid : ∀ i, cHiI P i ∈ Set.Icc (0 : ℝ) (cHiI P i) := fun i =>
    ⟨by unfold cHiI; linarith [(hlast i).1], le_rfl⟩
  constructor
  · rintro ⟨-, hrange, hIC⟩ i
    have h1 := hIC i _ (hmem i) _ (hbid i)
    have h2 := (hrange i _ (hmem i)).2
    have hW : 0 ≤ ∫ cv, winProbBIA P τ (Function.update (bidProfile βI cv) i
        (βI i (cHiI P i))) i ∂(costVecLaw P) := by
      apply integral_nonneg; intro cv
      unfold winProbBIA
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    unfold profitBIA at h1 ⊢
    simp only [sub_self, zero_mul] at h1
    apply le_antisymm _ h1
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hW
  · rintro ⟨-, hrange, hIC⟩ i
    have h1 := hIC i _ (hmem i) _ (hbid i)
    have h2 := (hrange i _ (hmem i)).2
    have hW : 0 ≤ ∫ cv, winProbBAI P (Function.update (bidProfile βA cv) i
        (βA i (cHiI P i))) i ∂(costVecLaw P) := by
      apply integral_nonneg; intro cv
      unfold winProbBAI winProbFPA
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    unfold profitBAI at h1 ⊢
    simp only [sub_self, zero_mul] at h1
    apply le_antisymm _ h1
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hW
