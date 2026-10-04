-- Prove2me | solution 1 for ResourceScheduling.Graph.emit_rows
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:36.466096+00:00
-- url     : https://prove2.me/submissions/711fbe11-c572-47cc-8ac0-f02928e21929

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_emit_row
import Theorems.Thm_ResourceScheduling_Graph_for_n_rule
import Theorems.Thm_ResourceScheduling_Graph_ram_field_frame

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe emitRows B s ∧ (emitRows.eval s).out =
      ((wordNonEdges N s.word).flatMap fun p => (List.range N).flatMap fun k =>
        unary (if k = p.1 ∨ k = p.2 then 1 else 0)).reverse ++ s.out := by
  let R := fun i => ((List.range N).filter fun j =>
    decide (i < j ∧ s.word.getD (i * N + j) Letter.sep ≠ Letter.one)).flatMap fun j =>
      (List.range N).flatMap fun k => unary (if k = i ∨ k = j then 1 else 0)
  let E := fun m => (List.range m).flatMap R
  let p := forN c1 j (by decide) (ifNonEdge (forN c2 k (by decide) emitCell))
  let P := fun m (x : RAMState GraphReg) => x.word = s.word ∧ x.out = (E m).reverse ++ s.out
  have hw : p.writes n = false ∧ p.writes i = false ∧ p.writes c0 = false := ⟨rfl,rfl,rfl⟩
  have hword (x : RAMState GraphReg) : (p.eval x).word = x.word := ram_field_frame p true (by rfl) x
  have hr := for_n_rule c0 i (by decide) (by decide) (by decide) p hw B N P
    (by intro m x a; simp [P, RAMState.set]) (by intro m x a; simp [P, RAMState.set])
    s hs hn (by simp [P, E]) (by
      intro m hm x hx hxn hxi hPx
      obtain ⟨hsafe,he⟩ := emit_row B N x hx (by omega) hxn hB hpos
      refine ⟨hsafe, (hword x).trans hPx.1, ?_⟩
      rw [hPx.1, hxi, hPx.2] at he
      change (p.eval x).out = (E (m + 1)).reverse ++ s.out
      rw [he]
      simp [E, R, List.range_succ, List.reverse_append, List.append_assoc])
  refine ⟨hr.1, ?_⟩
  simpa [P, E, R, p, emitRows, wordNonEdges, List.flatMap_assoc, List.flatMap_map] using hr.2.2.2.2

#print axioms solution
