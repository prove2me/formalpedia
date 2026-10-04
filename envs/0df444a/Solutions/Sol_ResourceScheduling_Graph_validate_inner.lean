-- Prove2me | solution 1 for ResourceScheduling.Graph.validate_inner
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:20.337969+00:00
-- url     : https://prove2.me/submissions/a2acb7e2-4fe3-41b8-9708-5a9d96f16985

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_for_n_rule
import Theorems.Thm_ResourceScheduling_Graph_validate_cell_safe
import Theorems.Thm_ResourceScheduling_Graph_cells_eval
import Theorems.Thm_ResourceScheduling_Graph_ram_field_frame
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe (forN c1 j (by decide) validateCell) B s ∧
    ((forN c1 j (by decide) validateCell).eval s).val good =
      if ∀ j < N, s.word.getD (s.val i * N + j) Letter.sep = Letter.one →
        s.word.getD (j * N + s.val i) Letter.sep = Letter.one then s.val good else 0 := by
  let C := fun j => s.word.getD (s.val i * N + j) Letter.sep = Letter.one →
    s.word.getD (j * N + s.val i) Letter.sep = Letter.one
  let P := fun k (x : RAMState GraphReg) => x.word = s.word ∧ x.val i = s.val i ∧
    x.val good = if ∀ j < k, C j then s.val good else 0
  have hw : validateCell.writes n = false ∧ validateCell.writes j = false ∧
      validateCell.writes c1 = false := by simp [validateCell, GraphProgram.read, block, RAMCode.writes]
  have hxword (x : RAMState GraphReg) : (validateCell.eval x).word = x.word :=
    ram_field_frame validateCell true (by rfl) x
  have hxi (x : RAMState GraphReg) : (validateCell.eval x).val i = x.val i :=
    ram_footprint validateCell i (by rfl) x
  have hr := for_n_rule c1 j (by decide) (by decide) (by decide) validateCell hw B N P
    (by intro k x a; simp [P, RAMState.set]) (by intro k x a; simp [P, RAMState.set])
    s hs hn (by simp [P]) (by
      intro k hk x hx hxn hxj hPx
      have hsafe := validate_cell_safe B N x hx (by rw [hPx.2.1]; exact hi)
        (by omega) (by omega) hB hpos
      refine ⟨hsafe, (hxword x).trans hPx.1, (hxi x).trans hPx.2.1, ?_⟩
      have hg := (cells_eval x).1
      rw [hPx.1, hPx.2.1, hxn, hxj, hPx.2.2] at hg
      change (validateCell.eval x).val good = if ∀ j < k + 1, C j then s.val good else 0
      rw [hg]
      simp only [Nat.forall_lt_succ_right]
      by_cases ha : ∀ j < k, C j <;> by_cases hb : C k <;> simp_all [C])
  exact ⟨hr.1, hr.2.2.2.2.2⟩

#print axioms solution
