-- Prove2me | solution 1 for UlmsTheorem.pPow_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:53:30.098423+00:00
-- url     : https://prove2.me/submissions/4e01cb18-2a6a-46b6-9e45-0b595b1bf652

module
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution : pPow p 0 (G := G) = ⊤ := by
  ext x
  simp [pow_zero, one_smul]
end UlmsTheorem
