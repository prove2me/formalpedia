-- Prove2me | solution 1 for SinkReset.Plan.within_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:59.081547+00:00
-- url     : https://prove2.me/submissions/265f52af-e0c5-497a-b16a-603dda1d7352

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
theorem _root_.solution (b : ℕ) :
    Within A Finset.univ b ↔ ∃ w, A.IsReset w ∧ w.length ≤ b := by
  constructor
  · rintro ⟨w, ⟨hw, hw0⟩, hlen⟩
    exact ⟨w, ⟨hw, fun q => hw0 q (Finset.mem_univ q)⟩, hlen⟩
  · rintro ⟨w, ⟨hw, hw0⟩, hlen⟩
    exact ⟨w, ⟨hw, fun q _ => hw0 q⟩, hlen⟩
end SinkReset.Plan
