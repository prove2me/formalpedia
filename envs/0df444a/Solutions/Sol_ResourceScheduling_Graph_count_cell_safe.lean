-- Prove2me | solution 1 for ResourceScheduling.Graph.count_cell_safe
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:21.59864+00:00
-- url     : https://prove2.me/submissions/a6e704b6-f608-40f2-be19-fc6eea0943b3

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_non_edge_safe
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hj : s.val j ≤ N) (hn : s.val n ≤ N)
    (hc : s.val count + 1 ≤ B) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (ifNonEdge (.inc count)) B s := by
  exact non_edge_safe (.inc count) B N (fun x => x.val count + 1 ≤ B) (by
    intro v hv x a hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> simpa [RAMState.set] using hx)
    (fun x hx hc => ⟨hx, ram_bound_set B x hx count _ hc⟩)
    s hs hc hi hj hn hB hpos

#print axioms solution
