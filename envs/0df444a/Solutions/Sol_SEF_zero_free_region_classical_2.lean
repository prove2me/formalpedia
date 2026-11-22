-- Prove2me | solution 2 for SEF.zero_free_region_classical
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:36:02.67621+00:00
-- url     : https://prove2.me/submissions/1dc8f93b-a202-4f03-b509-f68bc491ad71
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SEF_theta
import Definitions.Def_SEF_hecke
import Theorems.Thm_mathlib_riemannHypothesis



namespace SEF
end SEF
open SEF
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ σ t : ℝ, 1 - c / Real.log (|t| + 2) ≤ σ → riemannZeta ⟨σ, t⟩ ≠ 0 :=
  by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 4, div_pos hlog2 (by norm_num), ?_⟩
  intro σ t hσ hz
  have hlog : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hfrac : Real.log 2 / 4 / Real.log (|t| + 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hre : (3 / 4 : ℝ) ≤ σ := by linarith
  have htriv : ¬∃ n : ℕ, (⟨σ, t⟩ : ℂ) = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have h := congrArg Complex.re hn
    simp at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  by_cases hone : (⟨σ, t⟩ : ℂ) = 1
  · rw [hone] at hz
    exact riemannZeta_one_ne_zero hz
  · have h : σ = 1 / 2 := mathlib_riemannHypothesis _ hz htriv hone
    linarith
