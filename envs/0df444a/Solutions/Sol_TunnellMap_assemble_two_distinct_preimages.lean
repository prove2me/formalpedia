-- Prove2me | solution 1 for TunnellMap.assemble_two_distinct_preimages
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:24.818567+00:00
-- url     : https://prove2.me/submissions/54b317ec-6efa-4233-9418-693d82b73d4c

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply


attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr

set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}
namespace TunnellMap
theorem _root_.solution (even : E ≃ A) (odd : O ≃ A)
    (a : A) :
    assemble even odd (Sum.inl (even.symm a)) = a ∧
      assemble even odd (Sum.inr (odd.symm a)) = a ∧
      Sum.inl (even.symm a) ≠ Sum.inr (odd.symm a) := by
  simp
end TunnellMap
