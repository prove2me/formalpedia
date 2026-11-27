-- Prove2me | solution 1 for PvsNP.OnlineMailbox.replay_halt
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-27T04:12:41.52604+00:00
-- url     : https://prove2.me/submissions/11439234-f17a-4055-9d28-de43fb294fc0

import Definitions.Def_OnlineBooleanMailbox

set_option autoImplicit false

namespace PvsNP.OnlineMailbox

variable {G C : Type}

theorem Steps.trans {S : Type} {tick : S → Option S} {a b c : S} {i j : ℕ}
    (p : Steps tick i a b) (q : Steps tick j b c) : Steps tick (i + j) a c := by
  induction p with
  | zero => simpa using q
  | @next n x y z h _ ih =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Steps.next h (ih q)

theorem Steps.one {S : Type} {tick : S → Option S} {a b : S}
    (h : tick a = some b) : Steps tick 1 a b :=
  Steps.next h (Steps.zero b)

theorem refill_waiting (p : Producer G) (c : Consumer C) (r : C)
    {x : Source G} {word : List Bool} {n : ℕ} (h : Produces p x word n) :
    ∃ (a : Source G) (used pending : ℕ),
      Steps (step p c) used (⟨x, r, .waiting⟩ : Combined G C)
        ⟨a, r, .ready word.head?⟩ ∧
      Pending p (.ready word.head?) a word pending ∧ used + pending = n + 1 := by
  induction h with
  | @halt x h =>
    exact ⟨x, 1, 0, Steps.one (by simp [step, h]), Pending.eof x, by simp⟩
  | @next x y out tail n h suffix ih =>
    cases out with
    | none =>
      obtain ⟨a, used, pending, run, hp, balance⟩ := ih
      refine ⟨a, used + 1, pending, Steps.next (y := ⟨y, r, .waiting⟩) ?_ run, hp, ?_⟩
      · simp [step, h]
      · omega
    | some b =>
      refine ⟨y, 1, n + 1, Steps.one ?_, Pending.bit suffix, ?_⟩
      · simp [step, h]
      · omega

theorem refill (p : Producer G) (c : Consumer C) (r : C)
    {x : Source G} {m : Mailbox} {word : List Bool} {n : ℕ} (h : Pending p m x word n) :
    ∃ (a : Source G) (used pending : ℕ),
      Steps (step p c) used (⟨x, r, m⟩ : Combined G C) ⟨a, r, .ready word.head?⟩ ∧
      Pending p (.ready word.head?) a word pending ∧ used + pending = n := by
  cases h with
  | waiting h => exact refill_waiting p c r h
  | bit h => exact ⟨_, 0, _, Steps.zero _, Pending.bit h, Nat.zero_add _⟩
  | eof x => exact ⟨x, 0, 0, Steps.zero _, Pending.eof x, rfl⟩

theorem pending_after_consumer (p : Producer G)
    {x : Source G} {word : List Bool} {n : ℕ} {symbol : Option Bool}
    (h : Pending p (.ready symbol) x word n) (advance : Bool) :
    Pending p (afterConsumer symbol advance) x (if advance then word.tail else word) n := by
  cases h with
  | bit h =>
    cases advance
    · simpa [afterConsumer] using Pending.bit h
    · simpa [afterConsumer] using Pending.waiting h
  | eof x => cases advance <;> simpa [afterConsumer] using Pending.eof (p := p) x

/-- Every finite consumer prefix is replayed exactly, leaving a coherent
mailbox. Completed transitions plus pending producer work equal the sum of
standalone consumer transitions and the initial producer budget. -/
theorem replay_prefix (p : Producer G) (c : Consumer C)
    {i : ℕ} {v w : Virtual C} (run : Steps (consume c) i v w)
    {x : Source G} {mailbox : Mailbox} {budget : ℕ} (h : Pending p mailbox x v.2 budget) :
    ∃ (y : Source G) (mailbox' : Mailbox) (used pending : ℕ),
      Steps (step p c) used (⟨x, v.1, mailbox⟩ : Combined G C) ⟨y, w.1, mailbox'⟩ ∧
      Pending p mailbox' y w.2 pending ∧ used + pending = i + budget := by
  induction run generalizing x mailbox budget with
  | zero v =>
      exact ⟨x, mailbox, 0, budget, Steps.zero _, h, by simp⟩
  | @next i v v' w next _ ih =>
    rcases v with ⟨r, word⟩
    cases hs : c r word.head? with
    | none => simp [consume, hs] at next
    | some result =>
      rcases result with ⟨r', advance⟩
      have hv : (r', if advance then word.tail else word) = v' := by
        simpa [consume, hs] using next
      subst v'
      obtain ⟨a, fill, remain, filled, valid, fillBalance⟩ := refill p c r h
      have dispatched : step p c ⟨a, r, .ready word.head?⟩ =
          some ⟨a, r', afterConsumer word.head? advance⟩ := by simp [step, hs]
      obtain ⟨y, final, used, pending, replay, consistent, replayBalance⟩ :=
        ih (pending_after_consumer p valid advance)
      refine ⟨y, final, fill + (used + 1), pending, filled.trans (Steps.next dispatched replay),
        consistent, ?_⟩
      omega

/-- A terminating consumer gets the same state and virtual input suffix in
the interleaved run. The combined machine can stop without running the
remaining producer transitions. -/
theorem replay_halt (p : Producer G) (c : Consumer C)
    {x : Source G} {out : List Bool} {g : ℕ} (producer : Produces p x out g)
    {r : C} {v : Virtual C} {i : ℕ} (run : Steps (consume c) i (r, out) v)
    (done : c v.1 v.2.head? = none) :
    ∃ (y : Source G) (used pending : ℕ),
      Steps (step p c) used (⟨x, r, .waiting⟩ : Combined G C)
        ⟨y, v.1, .ready v.2.head?⟩ ∧
      step p c ⟨y, v.1, .ready v.2.head?⟩ = none ∧
      Pending p (.ready v.2.head?) y v.2 pending ∧ used + pending = i + g + 1 := by
  obtain ⟨a, m, replay, remaining, path, valid, replayBalance⟩ :=
    replay_prefix p c run (Pending.waiting producer)
  obtain ⟨y, fill, pending, last, consistent, fillBalance⟩ := refill p c v.1 valid
  refine ⟨y, replay + fill, pending, path.trans last, ?_, consistent, ?_⟩
  · simp [step, done]
  · omega

end PvsNP.OnlineMailbox

open PvsNP.OnlineMailbox

theorem solution {G C : Type} (p : Producer G) (c : Consumer C)
    {x : Source G} {out : List Bool} {g : ℕ} (producer : Produces p x out g)
    {r : C} {v : Virtual C} {i : ℕ} (run : Steps (consume c) i (r, out) v)
    (done : c v.1 v.2.head? = none) :
    ∃ (y : Source G) (used pending : ℕ),
      Steps (step p c) used (⟨x, r, .waiting⟩ : Combined G C)
        ⟨y, v.1, .ready v.2.head?⟩ ∧
      step p c ⟨y, v.1, .ready v.2.head?⟩ = none ∧
      Pending p (.ready v.2.head?) y v.2 pending ∧ used + pending = i + g + 1 := by
  exact replay_halt p c producer run done

#print axioms solution
