-- Prove2me | solution 1 for TarskiQuasiFPT.UpperBound.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T15:48:51.328524+00:00
-- url     : https://prove2.me/submissions/7f4d6783-d063-4c15-ba86-6234c36c3ae2

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets
set_option autoImplicit false
open TarskiQuasiFPT.UpperBound

theorem solution {n k : ℕ} [NeZero n] (Q : QASet n k) (hQ : IsSafeQA Q) (s : Slice n k) :
    (∃ y : Point n k, IsPostfixed Q s y) ∧
    (∀ a b : Point n k, IsPostfixed Q s a → IsPostfixed Q s b → IsPostfixed Q s (a ⊔ b)) ∧
    (∃ y : Point n k, IsPrefixed Q s y) ∧
    (∀ a b : Point n k, IsPrefixed Q s a → IsPrefixed Q s b → IsPrefixed Q s (a ⊓ b)) := by
  classical
  let lo : Point n k := fun i => (s i).getD ⊥
  let hi : Point n k := fun i => (s i).getD ⊤
  refine ⟨⟨lo, ?_, ?_⟩, ?_, ⟨hi, ?_, ?_⟩, ?_⟩
  · intro i a hs
    simp [lo, hs]
  · intro h hm hc i hs
    simp [lo, hs]
  · intro a b ha hb
    constructor
    · intro i c hc
      have h1 := ha.1 i c hc
      have h2 := hb.1 i c hc
      simp [Pi.sup_apply, h1, h2]
    · intro h hm hc i hi
      have h1 := ha.2 h hm hc i hi
      have h2 := hb.2 h hm hc i hi
      have h3 := (hm (show a ≤ a ⊔ b from le_sup_left)).1 i
      have h4 := (hm (show b ≤ a ⊔ b from le_sup_right)).1 i
      exact sup_le (le_trans h1 h3) (le_trans h2 h4)
  · intro i a hs
    simp [hi, hs]
  · intro h hm hc i hs
    simp [hi, hs]
  · intro a b ha hb
    constructor
    · intro i c hc
      have h1 := ha.1 i c hc
      have h2 := hb.1 i c hc
      simp [Pi.inf_apply, h1, h2]
    · intro h hm hc i hi
      have h1 := ha.2 h hm hc i hi
      have h2 := hb.2 h hm hc i hi
      have h3 := (hm (show a ⊓ b ≤ a from inf_le_left)).1 i
      have h4 := (hm (show a ⊓ b ≤ b from inf_le_right)).1 i
      exact le_inf (le_trans h3 h1) (le_trans h4 h2)
#print axioms solution
