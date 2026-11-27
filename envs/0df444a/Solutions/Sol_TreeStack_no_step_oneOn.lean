-- Prove2me | solution 1 for TreeStack.no_step_oneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:15.809732+00:00
-- url     : https://prove2.me/submissions/d1a4f18d-a064-4f9f-bd42-55b9011ee921

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.oneOn_apply
attribute [local simp] TreeStack.mass_oneOn

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (s : Finset V) {D : Configuration V} : ¬ PebbleStep G (oneOn s) D := by
  rintro ⟨u, v, -, hu, -⟩
  by_cases hus : u ∈ s <;> simp [oneOn, hus] at hu
end TreeStack
