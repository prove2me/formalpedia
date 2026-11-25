-- Prove2me | solution 1 for SinkReset.Plan.lift_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:03.728678+00:00
-- url     : https://prove2.me/submissions/a7ea0097-7e1f-42fd-96e6-1d5c02c0f1b2

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n m : ℕ} [NeZero n] [NeZero m]
variable (A : Automaton n) (B : Automaton m) (τ : Letter n → Letter m)
namespace SinkReset.Plan
theorem _root_.solution
    (hletters : ∀ b, b ∈ B.letters ↔ ∃ a ∈ A.letters, τ a = b) (v : List (Letter m)) (hv : B.IsWord v) :
    ∃ u, A.IsWord u ∧ u.map τ = v ∧ u.length = v.length := by
  induction v with
  | nil => exact ⟨[], by simp [Automaton.IsWord], rfl, rfl⟩
  | cons b v ih =>
    have hb : b ∈ B.letters := hv b List.mem_cons_self
    obtain ⟨a, ha, rfl⟩ := (hletters b).1 hb
    obtain ⟨u, hu, hmap, hlen⟩ := ih fun c hc => hv c (List.mem_cons_of_mem _ hc)
    refine ⟨a :: u, ?_, by simp [hmap], by simp [hlen]⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ha
    · exact hu c hc
end SinkReset.Plan
