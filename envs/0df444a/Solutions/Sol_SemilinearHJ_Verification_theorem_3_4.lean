-- Prove2me | solution 1 for SemilinearHJ.Verification.theorem_3_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:21:53.202122+00:00
-- url     : https://prove2.me/submissions/23fd1b23-1b00-4c87-8f1d-dbee2e04d9bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting
import Theorems.Thm_SemilinearHJ_Verification_theorem_3_3

open SemilinearHJ.Verification
open scoped ENNReal MeasureTheory

theorem solution {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (Y : Set (E n)) (hYc : IsCompact Y) (hYX : Y ⊆ X)
    (W : E n → ℝ) (hWL : ∃ K : NNReal, LipschitzOnWith K W X) (hWY : ∀ y ∈ Y, W y = 0)
    (hatt : ∀ x ∈ X \ Y, ∃ T : ℝ, 0 < T ∧ ∃ φ : ℝ → E n, IsPath X T φ ∧ φ 0 = x ∧ φ T ∈ Y ∧
      pathCost X Ψ r T φ ≠ ⊤ ∧ (pathCost X Ψ r T φ).toReal = W x)
    (hsub : AESubsolNeg X Ψ r W) :
    ∀ x ∈ X, tgtVal X Ψ r Y x ≠ ⊤ ∧ (tgtVal X Ψ r Y x).toReal = W x := by
  -- Y is nonempty: X is nonempty, and either a point of X lies in Y or it reaches Y.
  have hXne : X.Nonempty := by
    obtain ⟨S, hS, rfl⟩ := hX
    obtain ⟨s, hs⟩ := hS
    exact ⟨s, subset_convexHull ℝ _ hs⟩
  have hYne : Y.Nonempty := by
    obtain ⟨x0, hx0⟩ := hXne
    by_cases h : x0 ∈ Y
    · exact ⟨x0, h⟩
    · obtain ⟨T, -, φ, -, -, hφT, -⟩ := hatt x0 ⟨hx0, h⟩
      exact ⟨φ T, hφT⟩
  obtain ⟨hfin, -, -, hzero, hmax⟩ := theorem_3_3 X hX Ψ hΨL hΨ0 r hr Y hYc hYX hYne
  intro x hx
  refine ⟨hfin x hx, le_antisymm ?_ (hmax W hWL hsub hWY x hx)⟩
  by_cases hxY : x ∈ Y
  · rw [hzero x hxY, hWY x hxY]
  · obtain ⟨T, -, φ, hφ, hφ0, hφT, hfinφ, hcost⟩ := hatt x ⟨hx, hxY⟩
    have hle : tgtVal X Ψ r Y x ≤ pathCost X Ψ r T φ := by
      unfold tgtVal
      exact iInf_le_of_le T (iInf_le_of_le φ (iInf_le_of_le ⟨hφ, hφ0, hφT⟩ le_rfl))
    rw [← hcost]
    exact ENNReal.toReal_mono hfinφ hle
