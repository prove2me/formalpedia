-- Prove2me | solution 1 for SinkReset.Plan.trap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:58.007822+00:00
-- url     : https://prove2.me/submissions/98babbcb-19be-4c06-ad7a-ee4f5fbd113a

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
section
@[expose] public section
namespace SinkReset
namespace Plan
section Basic
variable {n : ℕ} [NeZero n] (A : Automaton n)
private theorem trap_aux {k : ℕ} (T : Finset (Fin n)) (hzero : 0 ∉ T)
    (hreply : ∀ t ∈ T, ∀ a ∈ A.letters, ∃ u,
      A.IsWord u ∧ u.length < k ∧ act (a :: u) t ∈ T)
    {S : Finset (Fin n)} (h : A.AliceWins k S) : ∀ t ∈ S, t ∉ T := by
  induction h with
  | reset S hS =>
    intro t ht htT
    exact hzero (hS t ht ▸ htT)
  | step S a ha _ ih =>
    intro t ht htT
    obtain ⟨u, hu, hlen, hT⟩ := hreply t htT a ha
    exact ih u hu hlen _ (Finset.mem_image_of_mem _ ht) hT
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
theorem _root_.solution {k : ℕ} (T : Finset (Fin n)) (hne : T.Nonempty) (hzero : 0 ∉ T)
    (hreply : ∀ t ∈ T, ∀ a ∈ A.letters, ∃ u,
      A.IsWord u ∧ u.length < k ∧ act (a :: u) t ∈ T) :
    ¬ A.IsAk k := by
  intro h
  obtain ⟨t, ht⟩ := hne
  exact trap_aux A T hzero hreply h t (Finset.mem_univ t) ht
end SinkReset.Plan
