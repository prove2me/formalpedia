-- Prove2me | solution 2 for Psi.noDescent_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:49:42.905868+00:00
-- url     : https://prove2.me/submissions/32c014c5-af8c-4e23-bda1-a5025b55a1ba

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_noDescent_of_desc

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (w' : List Bool) (hb : 1 ≤ b) :
    noDescent (List.replicate a false ++ List.replicate b true ++ false :: w') = false := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have heq : List.replicate a false ++ List.replicate (b' + 1) true ++ false :: w'
       = (List.replicate a false ++ List.replicate b' true) ++ true :: false :: w' := by
    rw [List.replicate_succ']; simp [List.append_assoc]
  rw [heq]; exact noDescent_of_desc _ _
end Psi
