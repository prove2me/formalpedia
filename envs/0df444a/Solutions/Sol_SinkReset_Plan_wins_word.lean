-- Prove2me | solution 1 for SinkReset.Plan.wins_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:06.91675+00:00
-- url     : https://prove2.me/submissions/b7a17f99-c989-4861-9abc-f415fe5c9de0

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    (h : A.AliceWins k S) : ∃ w, ResetOn A S w := by
  induction h with
  | reset S hS => exact ⟨[], fun a ha => by simp at ha, fun q hq => hS q hq⟩
  | step S a ha _ ih =>
    obtain ⟨w, hw, hw0⟩ := ih [] (fun b hb => by simp at hb) (by simp only [List.length_nil]; omega)
    refine ⟨a :: w, fun b hb => ?_, fun q hq => ?_⟩
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hw b hb
    · exact hw0 _ (Finset.mem_image_of_mem _ hq)
end SinkReset.Plan
