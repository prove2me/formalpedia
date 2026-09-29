-- Prove2me | solution 1 for OnlineConvexOpt.Introduction.no_deterministic_algorithm_beats_double_mistakes
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:18:16.327546+00:00
-- url     : https://prove2.me/submissions/69ef3533-6c25-4036-880b-9d2ff7449b14

import Mathlib
import Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts

namespace OnlineConvexOpt.Introduction

theorem oc_no_det (alg : (ℕ → Bool) → ℕ → Bool)
    (halg : ∀ outcome₁ outcome₂ : ℕ → Bool, ∀ t : ℕ,
      (∀ s, s < t → outcome₁ s = outcome₂ s) → alg outcome₁ t = alg outcome₂ t)
    (T : ℕ) :
    ∃ outcome : ℕ → Bool,
      algMistakes (alg outcome) outcome T = T ∧
      (T : ℝ) ≥
        2 * (min ((Finset.range T).filter (fun t => outcome t = false)).card
                  ((Finset.range T).filter (fun t => outcome t = true)).card : ℝ) := by
  let seq : ℕ → ℕ → Bool := fun n =>
    Nat.rec (fun _ => false) (fun t f => Function.update f t (!(alg f t))) n
  have hseq0 : seq 0 = fun _ => false := rfl
  have hseqS : ∀ t, seq (t + 1) = Function.update (seq t) t (!(alg (seq t) t)) := fun t => rfl
  have hstab : ∀ t s, s < t → seq t s = seq (s + 1) s := by
    intro t
    induction t with
    | zero => intro s hs; exact absurd hs (Nat.not_lt_zero s)
    | succ t ih =>
      intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
      · rw [hseqS, Function.update_of_ne (Nat.ne_of_lt h), ih s h]
      · rw [h]
  let outcome : ℕ → Bool := fun t => seq (t + 1) t
  have hagree : ∀ t s, s < t → outcome s = seq t s := fun t s hs => (hstab t s hs).symm
  have herr : ∀ t, alg outcome t ≠ outcome t := by
    intro t
    have h1 : alg outcome t = alg (seq t) t := halg _ _ t (fun s hs => hagree t s hs)
    have h2 : outcome t = !(alg (seq t) t) := by
      show seq (t + 1) t = _
      rw [hseqS, Function.update_self]
    rw [h1, h2]
    cases alg (seq t) t <;> decide
  refine ⟨outcome, ?_, ?_⟩
  · unfold algMistakes
    rw [Finset.filter_true_of_mem (fun t _ => herr t), Finset.card_range]
  · have hsum : ((Finset.range T).filter (fun t => outcome t = false)).card +
        ((Finset.range T).filter (fun t => outcome t = true)).card = T := by
      have := Finset.card_filter_add_card_filter_not
        (s := Finset.range T) (fun t => outcome t = false)
      rw [Finset.card_range] at this
      have e : (Finset.range T).filter (fun t => outcome t = true) =
          (Finset.range T).filter (fun a => ¬ outcome a = false) := by
        ext t; simp
      rw [e]; exact this
    have h1 := min_le_left (((Finset.range T).filter (fun t => outcome t = false)).card : ℝ)
      (((Finset.range T).filter (fun t => outcome t = true)).card : ℝ)
    have h2 := min_le_right (((Finset.range T).filter (fun t => outcome t = false)).card : ℝ)
      (((Finset.range T).filter (fun t => outcome t = true)).card : ℝ)
    have h3 : (((Finset.range T).filter (fun t => outcome t = false)).card : ℝ) +
        (((Finset.range T).filter (fun t => outcome t = true)).card : ℝ) = T := by
      exact_mod_cast hsum
    linarith

end OnlineConvexOpt.Introduction

open OnlineConvexOpt.Introduction

theorem solution
    (alg : (ℕ → Bool) → ℕ → Bool)
    (halg : ∀ outcome₁ outcome₂ : ℕ → Bool, ∀ t : ℕ,
      (∀ s, s < t → outcome₁ s = outcome₂ s) → alg outcome₁ t = alg outcome₂ t)
    (T : ℕ) :
    ∃ outcome : ℕ → Bool,
      algMistakes (alg outcome) outcome T = T ∧
      (T : ℝ) ≥
        2 * (min ((Finset.range T).filter (fun t => outcome t = false)).card
                  ((Finset.range T).filter (fun t => outcome t = true)).card : ℝ) := by
  exact oc_no_det alg halg T
