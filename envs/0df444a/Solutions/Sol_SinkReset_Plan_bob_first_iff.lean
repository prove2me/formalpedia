-- Prove2me | solution 1 for SinkReset.Plan.bob_first_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:31.081605+00:00
-- url     : https://prove2.me/submissions/83ad8edb-8233-4504-8962-8bc3830389df

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_wins_mono
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem act_nil (q : Fin n) : act ([] : List (Letter n)) q = q := rfl
private theorem word_nil : A.IsWord [] := by simp [Automaton.IsWord]
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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) :
    A.IsAk k ↔ ∀ u, A.IsWord u → u.length < k →
      A.AliceWins k (Finset.univ.image (act u)) := by
  constructor
  · intro h u _ _
    exact wins_mono A h (Finset.subset_univ _)
  · intro h
    have := h [] (word_nil A) (by simp only [List.length_nil]; omega)
    have he : (Finset.univ.image (act ([] : List (Letter n)))) = Finset.univ := by
      ext q; simp [act_nil]
    rw [he] at this
    exact this
end SinkReset.Plan
