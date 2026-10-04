-- Prove2me | solution 1 for ResourceScheduling.Graph.emit_row
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:34.801129+00:00
-- url     : https://prove2.me/submissions/23873920-3775-4f66-84cb-46760b31e7bc

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_emit_pair
import Theorems.Thm_ResourceScheduling_Graph_for_n_rule
import Theorems.Thm_ResourceScheduling_Graph_ram_field_frame
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (forN c1 j (by decide) (ifNonEdge (forN c2 k (by decide) emitCell))) B s ∧
    ((forN c1 j (by decide) (ifNonEdge (forN c2 k (by decide) emitCell))).eval s).out =
      (((List.range N).filter fun j => decide (s.val i < j ∧
        s.word.getD (s.val i * N + j) Letter.sep ≠ Letter.one)).flatMap fun j =>
          (List.range N).flatMap fun k => unary (if k = s.val i ∨ k = j then 1 else 0)).reverse ++ s.out := by
  let C := fun j => decide (s.val i < j ∧ s.word.getD (s.val i * N + j) Letter.sep ≠ Letter.one)
  let F := fun j => (List.range N).flatMap fun k => unary (if k = s.val i ∨ k = j then 1 else 0)
  let E := fun m => ((List.range m).filter C).flatMap F
  let p := ifNonEdge (forN c2 k (by decide) emitCell)
  let P := fun m (x : RAMState GraphReg) => x.word = s.word ∧ x.val i = s.val i ∧
    x.out = (E m).reverse ++ s.out
  have hw : p.writes n = false ∧ p.writes j = false ∧ p.writes c1 = false := ⟨rfl,rfl,rfl⟩
  have hword (x : RAMState GraphReg) : (p.eval x).word = x.word := ram_field_frame p true (by rfl) x
  have hival (x : RAMState GraphReg) : (p.eval x).val i = x.val i := ram_footprint p i (by rfl) x
  have hr := for_n_rule c1 j (by decide) (by decide) (by decide) p hw B N P
    (by intro m x a; simp [P, RAMState.set]) (by intro m x a; simp [P, RAMState.set])
    s hs hn (by simp [P, E]) (by
      intro m hm x hx hxn hxj hPx
      obtain ⟨hsafe,he⟩ := emit_pair B N x hx (by rw [hPx.2.1]; exact hi) (by omega) hxn hB hpos
      refine ⟨hsafe, (hword x).trans hPx.1, (hival x).trans hPx.2.1, ?_⟩
      rw [hPx.1, hPx.2.1, hxj, hPx.2.2] at he
      change (p.eval x).out = (E (m + 1)).reverse ++ s.out
      rw [he]
      by_cases hc : s.val i < m ∧ s.word.getD (s.val i * N + m) Letter.sep ≠ Letter.one
      all_goals simp only [List.getD_eq_getElem?_getD] at hc
      all_goals simp [E, F, C, List.range_succ, hc, List.reverse_append, List.append_assoc])
  exact ⟨hr.1, hr.2.2.2.2.2⟩

#print axioms solution
