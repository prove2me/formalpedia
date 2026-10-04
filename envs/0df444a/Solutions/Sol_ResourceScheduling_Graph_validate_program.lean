-- Prove2me | solution 1 for ResourceScheduling.Graph.validate_program
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:26.337872+00:00
-- url     : https://prove2.me/submissions/6d43b2ab-0efb-4b8b-9b2f-55300d261c90

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_validate_row
import Theorems.Thm_ResourceScheduling_Graph_for_n_rule
import Theorems.Thm_ResourceScheduling_Graph_ram_field_frame

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe validate B s ∧ (validate.eval s).val good =
      if ∀ i < N, s.word.getD (i * N + i) Letter.sep ≠ Letter.one ∧
        ∀ j < N, s.word.getD (i * N + j) Letter.sep = Letter.one →
          s.word.getD (j * N + i) Letter.sep = Letter.one then s.val good else 0 := by
  let C := fun i => s.word.getD (i * N + i) Letter.sep ≠ Letter.one ∧
    ∀ j < N, s.word.getD (i * N + j) Letter.sep = Letter.one →
      s.word.getD (j * N + i) Letter.sep = Letter.one
  let P := fun k (x : RAMState GraphReg) => x.word = s.word ∧
    x.val good = if ∀ i < k, C i then s.val good else 0
  have hw : validateRow.writes n = false ∧ validateRow.writes i = false ∧
      validateRow.writes c0 = false := by
    simp [validateRow, validateCell, GraphProgram.read, block, forN, RAMCode.writes]
  have hword (x : RAMState GraphReg) : (validateRow.eval x).word = x.word :=
    ram_field_frame validateRow true (by rfl) x
  have hr := for_n_rule c0 i (by decide) (by decide) (by decide) validateRow hw B N P
    (by intro k x a; simp [P, RAMState.set]) (by intro k x a; simp [P, RAMState.set])
    s hs hn (by simp [P]) (by
      intro k hk x hx hxn hxi hPx
      obtain ⟨hsafe,hg⟩ := validate_row B N x hx (by omega) hxn hB hpos
      refine ⟨hsafe, (hword x).trans hPx.1, ?_⟩
      rw [hPx.1, hxi, hPx.2] at hg
      change (validateRow.eval x).val good = if ∀ i < k + 1, C i then s.val good else 0
      rw [hg]
      simp only [Nat.forall_lt_succ_right]
      change (if C k then (if ∀ i < k, C i then s.val good else 0) else 0) =
        if (∀ i < k, C i) ∧ C k then s.val good else 0
      by_cases ha : ∀ i < k, C i <;> by_cases hb : C k <;> simp [ha, hb])
  exact ⟨hr.1, hr.2.2.2.2⟩

#print axioms solution
