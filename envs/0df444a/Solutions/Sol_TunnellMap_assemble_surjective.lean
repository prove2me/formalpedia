-- Prove2me | solution 1 for TunnellMap.assemble_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:24.148801+00:00
-- url     : https://prove2.me/submissions/c4b7d4bc-bd20-4f2e-b325-21da0765444f

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
theorem _root_.solution (even : E ≃ A) (odd : O ≃ A) :
    Function.Surjective (assemble even odd) := by
  intro a
  exact ⟨Sum.inl (even.symm a), by simp⟩
end TunnellMap
