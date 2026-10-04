-- Prove2me | solution 1 for ResourceScheduling.Graph.validate_row
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T16:01:23.037414+00:00
-- url     : https://prove2.me/submissions/b0681f15-2880-467f-ae79-067a79e16e41

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMFields
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
import Theorems.Thm_ResourceScheduling_Graph_validate_inner
import Theorems.Thm_ResourceScheduling_Graph_read_safe
import Theorems.Thm_ResourceScheduling_Graph_read_eval
import Theorems.Thm_ResourceScheduling_Graph_ram_bound_set
import Theorems.Thm_ResourceScheduling_Graph_ram_safe_laws
import Theorems.Thm_ResourceScheduling_Graph_ram_field_frame
import Theorems.Thm_ResourceScheduling_Graph_ram_footprint

set_option autoImplicit false
open ResourceScheduling.Graph GraphReg GraphProgram

theorem solution (B N : ℕ) (s : RAMState GraphReg) (hs : RAMBound B s)
    (hi : s.val i ≤ N) (hn : s.val n = N) (hB : N * N + N ≤ B) (hpos : 1 ≤ B) :
    RAMSafe validateRow B s ∧ (validateRow.eval s).val good =
      if s.word.getD (s.val i * N + s.val i) Letter.sep ≠ Letter.one ∧
        ∀ j < N, s.word.getD (s.val i * N + j) Letter.sep = Letter.one →
          s.word.getD (j * N + s.val i) Letter.sep = Letter.one then s.val good else 0 := by
  let r := read i i bitA (by decide)
  let q : Code := .branch bitA (.zero good) .skip
  let x := r.eval s
  let diag := block [r,q]
  let y := diag.eval s
  have hr := read_safe i i bitA (by decide) B N s hs hi (by omega) hi hB hpos
  have hzero : RAMSafe (.zero good : Code) B x :=
    ⟨hr.2, ram_bound_set B x hr.2 good 0 (Nat.zero_le _)⟩
  have hq : RAMSafe q B x := (ram_safe_laws (.zero good) .skip bitA B x).2.2 hzero ⟨hr.2,hr.2⟩
  have hyn : y.val n = N := (ram_footprint diag n (by rfl) s).trans hn
  have hyi : y.val i = s.val i := ram_footprint diag i (by rfl) s
  have hyword : y.word = s.word := ram_field_frame diag true (by rfl) s
  have hg : y.val good = if s.word.getD (s.val i * N + s.val i) Letter.sep = Letter.one
      then 0 else s.val good := by
    by_cases h : s.word.getD (s.val i * N + s.val i) Letter.sep = Letter.one
    all_goals
      simp only [List.getD_eq_getElem?_getD] at h
      simp [y, diag, r, q, block, RAMCode.eval, read_eval, RAMState.set, hn, h]
  have hv := validate_inner B N y hq.2 (by omega) hyn hB hpos
  have he : validateRow.eval s = (forN c1 j (by decide) validateCell).eval y := rfl
  refine ⟨⟨⟨hr.1, hq.1, hv.1.1, hv.1.2⟩, hv.1.2⟩, ?_⟩
  rw [he, hv.2, hyword, hyi, hg]
  split_ifs <;> simp_all <;> aesop

#print axioms solution
