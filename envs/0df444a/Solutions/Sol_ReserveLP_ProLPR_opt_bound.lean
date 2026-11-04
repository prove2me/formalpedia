-- Prove2me | solution 1 for ReserveLP.ProLPR.opt_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:02:10.933874+00:00
-- url     : https://prove2.me/submissions/51fc290e-aaab-445c-a8cc-7a63d314fd11

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model
import Theorems.Thm_ReserveLP_ProLPR_corollary_5_6
import Theorems.Thm_ReserveLP_ProLPR_lemma_5_7
import Theorems.Thm_ReserveLP_ProLPR_lemma_5_8

open ReserveLP.ProLPR

theorem solution (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    OPT n θ ≤ cStar := by
  apply corollary_5_6 n hn θ hθ cStar
  intro k hk
  refine ⟨lemma_5_7 θ hθ k hk, ?_⟩
  obtain ⟨h1, h2⟩ := lemma_5_8 θ hθ k hk
  linarith
