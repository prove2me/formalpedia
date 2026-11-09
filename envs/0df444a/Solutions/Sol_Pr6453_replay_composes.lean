-- Prove2me | solution 1 for Pr6453.replay_composes
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T19:09:29.678537+00:00
-- url     : https://prove2.me/submissions/e1b50a8d-fdc7-4052-a629-034fd59ac419

/-
PR #6453: composition and determinism of the replay.
-/
import Definitions.Def_Pr6453_Replay

set_option autoImplicit false

namespace Pr6453

theorem replay_composes :
    (∀ (n : ℕ) (p q : List (Event n)) (st : State n),
        replay? (p ++ q) st = (replay? p st).bind (replay? q)) ∧
      (∀ (n : ℕ) (prog : List (Event n)) (st fin fin' : State n),
        replay? prog st = some fin → replay? prog st = some fin' → fin = fin') := by
  refine ⟨?_, ?_⟩
  · intro n p q st
    induction p generalizing st with
    | nil => rfl
    | cons e es ih =>
        simp only [List.cons_append, replay?]
        rw [funext ih, Option.bind_assoc]
  · intro n prog st fin fin' h h'
    rw [h] at h'
    injection h' with h

end Pr6453

/-- **Replay composes and is deterministic.** -/
theorem solution :
    (∀ (n : ℕ) (p q : List (Pr6453.Event n)) (st : Pr6453.State n),
        Pr6453.replay? (p ++ q) st = (Pr6453.replay? p st).bind (Pr6453.replay? q)) ∧
      (∀ (n : ℕ) (prog : List (Pr6453.Event n)) (st fin fin' : Pr6453.State n),
        Pr6453.replay? prog st = some fin → Pr6453.replay? prog st = some fin' → fin = fin') :=
  Pr6453.replay_composes
