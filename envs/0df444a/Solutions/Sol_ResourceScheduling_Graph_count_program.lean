-- Prove2me | solution 1 for ResourceScheduling.Graph.count_program
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:27.111791+00:00
-- url     : https://prove2.me/submissions/9cb44d69-fd29-48ae-9191-1084b6f81913

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_count_inner
import Theorems.Thm_ResourceScheduling_Graph_for_n_rule
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set
import Theorems.Thm_ResourceScheduling_Graph_ram_field_frame

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

private theorem prefix_bound (N m : ℕ) (bits : List Letter) :
    ((List.range m).flatMap fun i => ((List.range N).filter fun j =>
      decide (i < j ∧ bits.getD (i * N + j) Letter.sep ≠ Letter.one)).map fun j => (i,j)).length ≤ m * N := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrow := List.length_filter_le (fun j =>
      decide (m < j ∧ bits.getD (m * N + j) Letter.sep ≠ Letter.one)) (List.range N)
    simp only [List.length_range] at hrow
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, List.length_map]
    nlinarith

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = N) (hB : N * N + N + 1 ≤ B) :
    RAMSafe countEdges B s ∧ (countEdges.eval s).val count = (wordNonEdges N s.word).length := by
  let E := fun m => (List.range m).flatMap fun i => ((List.range N).filter fun j =>
    decide (i < j ∧ s.word.getD (i * N + j) Letter.sep ≠ Letter.one)).map fun j => (i,j)
  let p := forN c1 j (by decide) (ifNonEdge (.inc count))
  let P := fun m (x : RAMState GraphReg) => x.word = s.word ∧ x.val count = (E m).length
  let s0 := s.set count 0
  have hs0 : RAMBound B s0 := ram_bound_set B s hs count 0 (Nat.zero_le _)
  have hw : p.writes n = false ∧ p.writes i = false ∧ p.writes c0 = false := ⟨rfl,rfl,rfl⟩
  have hword (x : RAMState GraphReg) : (p.eval x).word = x.word := ram_field_frame p true (by rfl) x
  have hr := for_n_rule c0 i (by decide) (by decide) (by decide) p hw B N P
    (by intro m x a; simp [P, RAMState.set]) (by intro m x a; simp [P, RAMState.set])
    s0 hs0 (by simpa [s0, RAMState.set] using hn) (by simp [P, E, s0, RAMState.set]) (by
      intro m hm x hx hxn hxi hPx
      have hlen : (E m).length ≤ N * N :=
        (prefix_bound N m s.word).trans (Nat.mul_le_mul_right N (by omega))
      have hc : x.val count + N + 1 ≤ B := by have := hPx.2; omega
      obtain ⟨hsafe,hcount⟩ := count_inner B N x hx (by omega) hxn hc (by omega) (by omega)
      refine ⟨hsafe, (hword x).trans hPx.1, ?_⟩
      rw [hPx.1, hxi, hPx.2] at hcount
      change (p.eval x).val count = (E (m + 1)).length
      rw [hcount]
      simp [E, List.range_succ])
  refine ⟨⟨⟨hs, hr.1.1, hr.1.2⟩, hr.1.2⟩, ?_⟩
  exact hr.2.2.2.2

#print axioms solution
