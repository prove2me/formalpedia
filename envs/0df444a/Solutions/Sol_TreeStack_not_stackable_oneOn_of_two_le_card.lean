-- Prove2me | solution 1 for TreeStack.not_stackable_oneOn_of_two_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:21.41136+00:00
-- url     : https://prove2.me/submissions/9f0152d5-c0f1-4bd5-835c-d5d2ef9ea407

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_no_step_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.oneOn_apply
attribute [local simp] TreeStack.mass_oneOn

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {s : Finset V} (hs : 2 ≤ s.card) :
    ¬ Stackable G (oneOn s) := by
  rintro ⟨r, D, hreach, hstack⟩
  rcases hreach.cases_head with hEq | ⟨E, hstep, -⟩
  · subst D
    have hr : r ∈ s := by
      by_contra hnr
      have hz : oneOn s r = 0 := by simp [oneOn, hnr]
      have hpos := hstack.1
      rw [hz] at hpos
      omega
    have hsub : s ⊆ {r} := by
      intro v hv
      simp only [Finset.mem_singleton]
      by_contra hvr
      have hz := hstack.2 v hvr
      simp [oneOn, hv] at hz
    have hcard : s.card ≤ 1 := by
      simpa using (Finset.card_le_card hsub)
    have : 2 ≤ 1 := le_trans hs hcard
    omega
  · exact no_step_oneOn s hstep
end TreeStack
