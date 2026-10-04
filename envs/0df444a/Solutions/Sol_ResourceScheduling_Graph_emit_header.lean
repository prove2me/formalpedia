-- Prove2me | solution 1 for ResourceScheduling.Graph.emit_header
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:02:51.246805+00:00
-- url     : https://prove2.me/submissions/69fc4243-f142-4da0-ae04-b62a50d373e3

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s) (hB : 2 ≤ B) :
    let p := block [.zero num, .inc num, .inc num, .emit num,
      .zero num, .inc num, .emit num, .emit n, .emit count]
    RAMSafe p B s ∧ p.eval s =
      { s.set num 1 with out :=
        (unary 2 ++ unary 1 ++ unary (s.val n) ++ unary (s.val count)).reverse ++ s.out } := by
  have h0 := ram_bound_set B s hs num 0 (by omega)
  have h1 := ram_bound_set B s hs num 1 (by omega)
  have h2 := ram_bound_set B s hs num 2 hB
  constructor
  · simpa [RAMSafe, RAMBound, block, RAMCode.Bounded, RAMCode.eval, RAMState.set] using
      (⟨⟨hs,h0,h1,h2,h2,h0,h1,h1,h1,h1⟩,h1⟩ :
        (RAMBound B s ∧ RAMBound B (s.set num 0) ∧ RAMBound B (s.set num 1) ∧
         RAMBound B (s.set num 2) ∧ RAMBound B (s.set num 2) ∧ RAMBound B (s.set num 0) ∧
         RAMBound B (s.set num 1) ∧ RAMBound B (s.set num 1) ∧ RAMBound B (s.set num 1) ∧
         RAMBound B (s.set num 1)) ∧ RAMBound B (s.set num 1))
  · simp [block, RAMCode.eval, RAMState.set, unary, List.reverse_append, List.append_assoc]

#print axioms solution
