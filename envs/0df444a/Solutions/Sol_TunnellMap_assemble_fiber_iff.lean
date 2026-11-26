-- Prove2me | solution 1 for TunnellMap.assemble_fiber_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:13.921934+00:00
-- url     : https://prove2.me/submissions/9d281ffd-17ae-4987-a7c2-25fddc3f5ade

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
theorem _root_.solution (even : E ≃ A) (odd : O ≃ A) (a : A)
    (x : E ⊕ O) :
    assemble even odd x = a ↔
      x = Sum.inl (even.symm a) ∨ x = Sum.inr (odd.symm a) := by
  cases x with
  | inl e =>
      simpa [assemble] using
        (even.apply_eq_iff_eq_symm_apply : even e = a ↔ e = even.symm a)
  | inr o =>
      simpa [assemble] using
        (odd.apply_eq_iff_eq_symm_apply : odd o = a ↔ o = odd.symm a)
end TunnellMap
