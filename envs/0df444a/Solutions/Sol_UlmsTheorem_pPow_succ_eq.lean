-- Prove2me | solution 1 for UlmsTheorem.pPow_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:53:34.721658+00:00
-- url     : https://prove2.me/submissions/3a818fd2-494a-422d-aa18-e3368ada2fba

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
theorem _root_.solution (n : ℕ) :
    (pPow p (G := G) (n + 1) : Set G) = {x | ∃ y ∈ pPow p (G := G) n, p • y = x} := by
  ext x
  simp only [pPow_mem_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨p ^ n • y, ⟨y, rfl⟩, by rw [← hy, smul_smul, mul_comm, ← pow_succ]⟩
  · rintro ⟨z, ⟨w, rfl⟩, hz⟩
    exact ⟨w, by rw [pow_succ, mul_comm, ← smul_smul]; exact hz⟩
end UlmsTheorem
