-- Prove2me | solution 1 for XinMartingaleInventory.Minimax.lemma_10
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:00:41.033416+00:00
-- url     : https://prove2.me/submissions/3be4547e-a0f0-4265-b171-c2975bd97c82

import Mathlib
import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

open XinMartingaleInventory.Minimax

theorem solution : ¬ (∀ (U μ : ℚ) (hU : 0 < U) (f : ℝ → ℝ)
    (hbounded : ∃ K : ℝ, ∀ d ∈ Set.Icc (0 : ℝ) (U : ℝ), |f d| ≤ K)
    (L R : ℝ) (hL : 0 ≤ L) (hLμ : L ≤ (μ : ℝ)) (hμR : (μ : ℝ) < R)
    (hRU : R ≤ (U : ℝ))
    (hmajor : ∀ d ∈ Set.Icc (0 : ℝ) (U : ℝ), f d ≤ chord f L R d),
    ∃ q : DemandLaw, q ∈ meanLaws U μ ∧ realAtoms q = realTwoPoint L R μ ∧
      ∀ q' ∈ meanLaws U μ,
        expectation q' (fun d => f (d : ℝ)) ≤ expectation q (fun d => f (d : ℝ))) := by
  intro h
  have hsqrt2_le : Real.sqrt 2 ≤ (2 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  obtain ⟨q, -, hq_atoms, -⟩ := h 3 2 (by norm_num) (fun _ => 0)
    ⟨0, fun d _ => by simp⟩ (Real.sqrt 2) 3 (Real.sqrt_nonneg 2)
    (by simp [hsqrt2_le]) (by norm_num) (by norm_num)
    (fun d _ => by simp [chord])
  have eval_L := congr_fun hq_atoms (Real.sqrt 2)
  have h_lhs : realAtoms q (Real.sqrt 2) = 0 := by
    unfold realAtoms
    have h_zero : (fun r : ℚ => if (r : ℝ) = Real.sqrt 2 then q r else 0) = fun _ => 0 := by
      ext r
      have hne : (r : ℝ) ≠ Real.sqrt 2 := (irrational_sqrt_two.ne_rat r).symm
      simp [hne]
    rw [h_zero, tsum_zero]
  have h_rhs : 0 < realTwoPoint (Real.sqrt 2) 3 (2 : ℚ) (Real.sqrt 2) := by
    unfold realTwoPoint
    have hne : Real.sqrt 2 ≠ 3 := by linarith
    simp only [ ↓reduceIte, hne, add_zero]
    exact div_pos (by norm_num) (by linarith)
  linarith
