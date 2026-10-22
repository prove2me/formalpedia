-- Prove2me | solution 1 for YeIPA.Random.lemma_6_14
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:48:44.03741+00:00
-- url     : https://prove2.me/submissions/5b2bcd6f-a68f-464a-a266-6fc0610bfa06

import Mathlib
import Definitions.Def_YeIPA_Random_Setting

open Matrix
open YeIPA.Random

theorem solution : ¬ (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m),
    (∃ x, IsFeasible65 A x) ↔
      ∃ (σ : Fin m ↪ Fin n) (x : Fin (m + 1) → ℝ), IsFeasible612 A σ x) := by
  intro H
  have hA : (0 : Matrix (Fin 0) (Fin 0) ℝ).rank = 0 := Matrix.rank_zero
  have h := (@H 0 0 0 hA).mpr ⟨Function.Embedding.refl _, fun _ => 1, by
    refine ⟨?_, ?_, ?_⟩
    · ext i; exact i.elim0
    · intro h0
      have := congrFun h0 0
      simp at this
    · intro k; norm_num⟩
  obtain ⟨x, _, _, hx⟩ := h
  exact hx (Subsingleton.elim _ _)
