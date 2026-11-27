-- Prove2me | solution 1 for SizeRamsey.Plan.incidentRed_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:24.284869+00:00
-- url     : https://prove2.me/submissions/3b2ff3b1-1836-4ce8-a606-d1c71cb07688

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_ColoringBase

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*}
    (F : SimpleGraph V) (S : Finset V) (u v : V) :
    (incidentRed F S).Adj u v ↔
      F.Adj u v ∧ (u ∈ S ∨ v ∈ S) := by
  simp only [incidentRed, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩
end SizeRamsey.Plan
