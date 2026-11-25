-- Prove2me | solution 1 for SinkReset.Plan.one_game_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:22.873921+00:00
-- url     : https://prove2.me/submissions/8c6d9c43-2913-40ee-8843-236d70e4e4d6

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem word_cons {a : Letter n} {u : List (Letter n)} :
    A.IsWord (a :: u) ↔ a ∈ A.letters ∧ A.IsWord u := by
  simp [Automaton.IsWord]
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
private theorem wins_word' {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (h : A.AliceWins k S) : ∃ w, A.IsWord w ∧ ∀ q ∈ S, act w q = 0 := by
  induction h with
  | reset S hS => exact ⟨[], word_nil A, fun q hq => hS q hq⟩
  | step S a ha _ ih =>
    obtain ⟨w, hw, hw0⟩ := ih [] (word_nil A) (by simp only [List.length_nil]; omega)
    refine ⟨a :: w, (word_cons A).2 ⟨ha, hw⟩, fun q hq => ?_⟩
    exact hw0 _ (Finset.mem_image_of_mem _ hq)
end Basic
section Transport
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
end Transport
section Upper
variable {n k : ℕ} [NeZero n] (A : Automaton n)
end Upper
end Plan
end SinkReset
end
end

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution : A.IsAk 1 ↔ ∃ w, A.IsReset w := by
  constructor
  · intro h
    obtain ⟨w, hw, hw0⟩ := wins_word' A le_rfl h
    exact ⟨w, hw, fun q => hw0 q (Finset.mem_univ q)⟩
  · rintro ⟨w, hw, hw0⟩
    suffices ∀ (w : List (Letter n)), A.IsWord w → ∀ S : Finset (Fin n),
        (∀ q ∈ S, act w q = 0) → A.AliceWins 1 S from this w hw _ fun q _ => hw0 q
    intro w
    induction w with
    | nil => intro _ S hS; exact .reset S hS
    | cons a w ih =>
      intro hw S hS
      rw [word_cons] at hw
      refine .step S a hw.1 fun u hu hlen => ?_
      have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hu0
      refine ih hw.2 _ fun q hq => ?_
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      exact hS p hp
end SinkReset.Plan
