-- Prove2me | solution 1 for ResourceScheduling.Graph.emit_inner
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:25.435152+00:00
-- url     : https://prove2.me/submissions/0ecd4970-c0cd-441c-99e5-186098f0f3bc

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_for_n_rule
import Theorems.Thm_ResourceScheduling_Graph_emit_cell_safe
import Theorems.Thm_ResourceScheduling_Graph_cells_eval
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = N) (hpos : 1 ≤ B) :
    RAMSafe (forN c2 k (by decide) emitCell) B s ∧
    ((forN c2 k (by decide) emitCell).eval s).out =
      ((List.range N).flatMap fun k => unary (if k = s.val i ∨ k = s.val j then 1 else 0)).reverse ++ s.out := by
  let F := fun k => unary (if k = s.val i ∨ k = s.val j then 1 else 0)
  let P := fun m (x : RAMState GraphReg) => x.val i = s.val i ∧ x.val j = s.val j ∧
    x.out = ((List.range m).flatMap F).reverse ++ s.out
  have hw : emitCell.writes n = false ∧ emitCell.writes k = false ∧ emitCell.writes c2 = false := ⟨rfl,rfl,rfl⟩
  have hival (x : RAMState GraphReg) : (emitCell.eval x).val i = x.val i := ram_footprint emitCell i (by rfl) x
  have hjval (x : RAMState GraphReg) : (emitCell.eval x).val j = x.val j := ram_footprint emitCell j (by rfl) x
  have hr := for_n_rule c2 k (by decide) (by decide) (by decide) emitCell hw B N P
    (by intro m x a; simp [P, RAMState.set]) (by intro m x a; simp [P, RAMState.set])
    s hs hn (by simp [P]) (by
      intro m hm x hx hxn hxk hPx
      refine ⟨emit_cell_safe B x hx hpos, (hival x).trans hPx.1, (hjval x).trans hPx.2.1, ?_⟩
      have hg := (cells_eval x).2.2
      rw [hPx.1, hPx.2.1, hxk, hPx.2.2] at hg
      change (emitCell.eval x).out = ((List.range (m + 1)).flatMap F).reverse ++ s.out
      rw [hg]
      simp [F, List.range_succ, List.reverse_append, List.append_assoc])
  exact ⟨hr.1, hr.2.2.2.2.2⟩

#print axioms solution
