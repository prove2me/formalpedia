-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_7_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:30.597255+00:00
-- url     : https://prove2.me/submissions/fb4e6d1b-a5ce-486d-845c-ed42a171cc82

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem



set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (A : RestrictedEquiv) (n : ℕ) {f x y : Pomega}
    (hf : ∀ a b, A.rel a b → A.rel (funOf f a) (funOf f b))
    (hxy : A.rel x y) :
    A.rel (Z n f x) (Z n f y) := by
  induction n with
  | zero => simpa [Z] using hxy
  | succ n ih =>
    simpa [Z] using hf _ _ ih
end Scott1976.DataTypesAsLattices
