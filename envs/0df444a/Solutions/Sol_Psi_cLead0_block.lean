-- Prove2me | solution 1 for Psi.cLead0_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:47:44.617826+00:00
-- url     : https://prove2.me/submissions/db6d7adc-0f3b-4f1a-9b5f-9637e41d70bd

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_P2M_Psi_cLead0_false__7e0ee6b4ef97
import Theorems.Thm_P2M_Psi_cLead0_true__7f4641256685

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (w' : List Bool) (hb : 1 ≤ b) :
    cLead0 (List.replicate a false ++ List.replicate b true ++ false :: w') = a := by
  induction a with
  | zero => obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append, cLead0_true']
  | succ n ih => rw [List.replicate_succ]; simp only [List.cons_append]; rw [cLead0_false', ih]; omega
end Psi
