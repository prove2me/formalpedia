-- Prove2me | solution 1 for SinkReset.Plan.wins_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:36.974641+00:00
-- url     : https://prove2.me/submissions/fc256486-464a-442f-aa80-56b83c6914d0

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem wins_of_rank' {n : ℕ} [NeZero n] (A : Automaton n) {k : ℕ} (rank : Finset (Fin n) → ℕ)
    (hstep : ∀ S : Finset (Fin n), (S.erase 0).Nonempty → ∃ a ∈ A.letters,
      ∀ u, A.IsWord u → u.length < k → rank (S.image (act (a :: u))) < rank S) :
    ∀ S, A.AliceWins k S := by
  intro S
  induction hr : rank S using Nat.strong_induction_on generalizing S with
  | _ r ih =>
    rcases (S.erase 0).eq_empty_or_nonempty with h | h
    · refine .reset S fun q hq => ?_
      by_contra hq0
      have : q ∈ S.erase 0 := Finset.mem_erase.2 ⟨hq0, hq⟩
      rw [h] at this; simp at this
    · obtain ⟨a, ha, hlt⟩ := hstep S h
      exact .step S a ha fun u hu hlen => ih _ (hr ▸ hlt u hu hlen) _ rfl
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
theorem _root_.solution {k : ℕ} (rank : Finset (Fin n) → ℕ)
    (hstep : ∀ S, (active S).Nonempty → ∃ a ∈ A.letters,
      ∀ u, A.IsWord u → u.length < k →
        rank (S.image (act (a :: u))) < rank S) :
    ∀ S, A.AliceWins k S :=
  wins_of_rank' A rank hstep
end SinkReset.Plan
