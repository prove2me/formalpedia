-- Prove2me | solution 1 for UlmsTheorem.mem_ulmSubgroup_nat_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:26.629173+00:00
-- url     : https://prove2.me/submissions/448cbb2a-d1bf-4b94-adbd-56f27468b761

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_nat

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (n : ℕ) (x : G) :
    x ∈ ulmSubgroup p (n : Ordinal) (G := G) ↔ ∃ y : G, p ^ n • y = x := by
  rw [ulmSubgroup_nat, pPow_mem_iff]
end UlmsTheorem
