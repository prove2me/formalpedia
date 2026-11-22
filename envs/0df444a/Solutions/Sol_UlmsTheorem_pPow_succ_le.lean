-- Prove2me | solution 1 for UlmsTheorem.pPow_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:53:30.674072+00:00
-- url     : https://prove2.me/submissions/359bb4e8-f3d3-4077-a2e1-3c4a6209a433

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
theorem _root_.solution (n : ℕ) : pPow p (n + 1) ≤ pPow p (G := G) n := by
  intro x ⟨y, hy⟩
  exact ⟨p • y, by rw [← hy, pow_succ, mul_smul]⟩
end UlmsTheorem
