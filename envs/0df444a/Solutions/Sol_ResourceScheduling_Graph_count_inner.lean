-- Prove2me | solution 1 for ResourceScheduling.Graph.count_inner
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:23.77704+00:00
-- url     : https://prove2.me/submissions/4e723d73-664e-4db6-9bd8-1fd9da75b329

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_for_n_rule
import Theorems.Thm_ResourceScheduling_Graph_count_cell_safe
import Theorems.Thm_ResourceScheduling_Graph_cells_eval
import Theorems.Thm_ResourceScheduling_Graph_ram_field_frame
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hn : s.val n = N) (hc : s.val count + N + 1 ≤ B)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (forN c1 j (by decide) (ifNonEdge (.inc count))) B s ∧
    ((forN c1 j (by decide) (ifNonEdge (.inc count))).eval s).val count = s.val count +
      ((List.range N).filter fun j => decide (s.val i < j ∧
        s.word.getD (s.val i * N + j) Letter.sep ≠ Letter.one)).length := by
  let C := fun j => decide (s.val i < j ∧ s.word.getD (s.val i * N + j) Letter.sep ≠ Letter.one)
  let p := ifNonEdge (.inc count)
  let P := fun k (x : RAMState GraphReg) => x.word = s.word ∧ x.val i = s.val i ∧
    x.val count = s.val count + ((List.range k).filter C).length
  have hw : p.writes n = false ∧ p.writes j = false ∧ p.writes c1 = false := ⟨rfl,rfl,rfl⟩
  have hword (x : RAMState GraphReg) : (p.eval x).word = x.word := ram_field_frame p true (by rfl) x
  have hival (x : RAMState GraphReg) : (p.eval x).val i = x.val i := ram_footprint p i (by rfl) x
  have hr := for_n_rule c1 j (by decide) (by decide) (by decide) p hw B N P
    (by intro k x a; simp [P, RAMState.set]) (by intro k x a; simp [P, RAMState.set])
    s hs hn (by simp [P]) (by
      intro k hk x hx hxn hxj hPx
      have hlen : ((List.range k).filter C).length ≤ k := by simpa using List.length_filter_le C (List.range k)
      have hcount : x.val count + 1 ≤ B := by have := hPx.2.2; omega
      have hsafe := count_cell_safe B N x hx (by rw [hPx.2.1]; exact hi)
        (by omega) (by omega) hcount hB hpos
      refine ⟨hsafe, (hword x).trans hPx.1, (hival x).trans hPx.2.1, ?_⟩
      have hg := (cells_eval x).2.1
      rw [hPx.1, hPx.2.1, hxn, hxj, hPx.2.2] at hg
      change (p.eval x).val count = s.val count + ((List.range (k + 1)).filter C).length
      rw [hg]
      by_cases h : s.val i < k ∧ s.word.getD (s.val i * N + k) Letter.sep ≠ Letter.one
      all_goals
        simp only [List.getD_eq_getElem?_getD] at h
        simp [C, List.range_succ, h, Nat.add_assoc])
  exact ⟨hr.1, hr.2.2.2.2.2⟩

#print axioms solution
