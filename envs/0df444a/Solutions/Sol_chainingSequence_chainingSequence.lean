-- Prove2me | solution 1 for chainingSequence_chainingSequence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:39:36.383158+00:00
-- url     : https://prove2.me/submissions/d386808b-51ee-4977-af37-575c2656408f

import Definitions.Def_BrownianMotion_Continuity_Chaining_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Chaining

### References
- https://arxiv.org/pdf/2107.13837.pdf Lemma 6.2
- Talagrand, The generic chaining
- Vershynin, High-Dimensional Probability (section 4.2 and chapter 8)

-/

@[expose] public section

open Metric
open scoped ENNReal NNReal

variable {E : Type*} {x y : E} {A : Set E} {C C₁ C₂ : Finset E} {ε ε₁ ε₂ : ℝ≥0}

variable [PseudoEMetricSpace E]

section Sequence

variable {ε : ℕ → ℝ≥0} {C : ℕ → Finset E} {k n : ℕ}

theorem AuxCh.rev_shift (C : ℕ → Finset E) (x : E) {k n : ℕ} (hn : n ≤ k) :
    ∀ j, j ≤ n → chainingSequenceReverse C x k (k - n + j)
      = chainingSequenceReverse C (chainingSequenceReverse C x k (k - n)) n j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [show k - n + (j + 1) = (k - n + j) + 1 by omega, chainingSequenceReverse_add_one,
      chainingSequenceReverse_add_one, ih (by omega)]
    congr 2
    omega

theorem _root_.solution (n : ℕ) (hn : n ≤ k) (m : ℕ) (hm : m ≤ n) :
    chainingSequence C (chainingSequence C x k n) n m = chainingSequence C x k m := by
  simp only [chainingSequence, if_pos hn, if_pos hm, if_pos (hm.trans hn)]
  have := AuxCh.rev_shift C x hn (n - m) (by omega)
  rw [show k - n + (n - m) = k - m by omega] at this
  exact this.symm

end Sequence
