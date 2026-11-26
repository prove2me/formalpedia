-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.chain_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:57.452921+00:00
-- url     : https://prove2.me/submissions/13456032-82c9-49fa-b991-568706bb2699

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    ∀ a b, a ≤ b → xs a ⊆ xs b := by
  intro a b hab
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  subst hd
  clear hab
  induction d with
  | zero => simp
  | succ d ih => exact subset_trans ih (hmono _)
end Scott1976.DataTypesAsLattices
