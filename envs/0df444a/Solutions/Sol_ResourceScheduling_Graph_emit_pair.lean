-- Prove2me | solution 1 for ResourceScheduling.Graph.emit_pair
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:34.062253+00:00
-- url     : https://prove2.me/submissions/dd8cc6d5-b5e5-4702-9160-78a624439038

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_emit_inner
import Theorems.Thm_ResourceScheduling_Graph_non_edge_safe
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set
import Theorems.Thm_ResourceScheduling_Graph_read_safe
import Theorems.Thm_ResourceScheduling_Graph_read_eval

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hj : s.val j ≤ N) (hn : s.val n = N)
    (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (ifNonEdge (forN c2 k (by decide) emitCell)) B s ∧
    ((ifNonEdge (forN c2 k (by decide) emitCell)).eval s).out =
      (if s.val i < s.val j ∧ s.word.getD (s.val i * N + s.val j) Letter.sep ≠ Letter.one
        then ((List.range N).flatMap fun k => unary (if k = s.val i ∨ k = s.val j then 1 else 0))
        else []).reverse ++ s.out := by
  let p := forN c2 k (by decide) emitCell
  have hsafe := non_edge_safe p B N (fun _ => True) (by simp)
    (by intro x hx _; exact (emit_inner B (x.val n) x hx rfl hpos).1)
    s hs trivial hi hj (by omega) hB hpos
  let x := s.set delta (s.val j - s.val i)
  let r := read i j bitA (by decide)
  let y := r.eval x
  have hx : RAMBound B x := ram_bound_set B s hs delta _ ((Nat.sub_le _ _).trans (hs.1 j))
  have hr := read_safe i j bitA (by decide) B N x hx
    (by simpa [x, RAMState.set] using hi) (by simpa [x, RAMState.set, hn])
    (by simpa [x, RAMState.set] using hj) hB hpos
  have hy : y = (x.set index (s.val i * N + s.val j)).set bitA
      (if s.word.getD (s.val i * N + s.val j) Letter.sep = Letter.one then 1 else 0) := by
    simpa [y, r, x, RAMState.set, hn] using read_eval i j bitA (by decide) x
  have he := (emit_inner B N y hr.2 (by simp [hy, x, RAMState.set, hn]) hpos).2
  have hout : (p.eval y).out =
      ((List.range N).flatMap fun k => unary (if k = s.val i ∨ k = s.val j then 1 else 0)).reverse ++ s.out := by
    simpa only [hy, x, RAMState.set, Function.update_of_ne (by decide : i ≠ bitA),
      Function.update_of_ne (by decide : i ≠ index), Function.update_of_ne (by decide : i ≠ delta),
      Function.update_of_ne (by decide : j ≠ bitA), Function.update_of_ne (by decide : j ≠ index),
      Function.update_of_ne (by decide : j ≠ delta)] using he
  refine ⟨hsafe, ?_⟩
  change ((ifNonEdge p).eval s).out = _
  have heval : (ifNonEdge p).eval s =
      if s.val i < s.val j then (if 0 < y.val bitA then y else p.eval y) else x := by
    simp only [ifNonEdge, block, List.foldr_cons, List.foldr_nil, RAMCode.eval]
    change (if 0 < s.val j - s.val i then (if 0 < y.val bitA then y else p.eval y) else x) = _
    simp only [Nat.sub_pos_iff_lt]
  have hbit : y.val bitA =
      if s.word.getD (s.val i * N + s.val j) Letter.sep = Letter.one then 1 else 0 := by
    simp only [hy, RAMState.set, Function.update_self]
  have hyo : y.out = s.out := by simp only [hy, x, RAMState.set]
  have hxo : x.out = s.out := rfl
  rw [heval]
  simp only [hbit]
  by_cases hij : s.val i < s.val j <;>
    by_cases hb : s.word.getD (s.val i * N + s.val j) Letter.sep = Letter.one
  all_goals simp only [List.getD_eq_getElem?_getD] at hb
  all_goals simp [hij, hb, hout, hyo, hxo]

#print axioms solution
