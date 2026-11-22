-- Prove2me | solution 1 for UlmsTheorem.pPow_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:24.515783+00:00
-- url     : https://prove2.me/submissions/e5cfc5f9-3740-4a29-b884-92f6e18e6f21

module
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Theorems.Thm_UlmsTheorem_pPow_succ_le

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution : Antitone (fun n ↦ pPow p n (G := G)) :=
  antitone_nat_of_succ_le (pPow_succ_le p)
end UlmsTheorem
