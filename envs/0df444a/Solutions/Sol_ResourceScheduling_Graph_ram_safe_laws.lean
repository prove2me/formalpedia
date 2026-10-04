-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_safe_laws
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T15:56:18.995654+00:00
-- url     : https://prove2.me/submissions/da9e53fa-d59f-47e4-b345-9afece07ace9

import Definitions.Def_ResourceScheduling_Graph_RAMSafe

set_option autoImplicit false
open ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (p q : RAMCode V) (v : V) (B : ℕ) (s : RAMState V) :
    (RAMBound B s → RAMSafe (.skip : RAMCode V) B s) ∧
    (RAMSafe p B s → RAMSafe q B (p.eval s) → RAMSafe (p.seq q) B s) ∧
    (RAMSafe p B s → RAMSafe q B s → RAMSafe (.branch v p q) B s) := by
  refine ⟨fun h => ⟨h, h⟩, ?_, ?_⟩
  · intro hp hq
    exact ⟨⟨hp.1, hq.1⟩, hq.2⟩
  · intro hp hq
    refine ⟨⟨hp.1, hq.1⟩, ?_⟩
    simp only [RAMCode.eval]
    split <;> first | exact hp.2 | exact hq.2

#print axioms solution
