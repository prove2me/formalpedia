-- Prove2me | solution 1 for UlmsTheorem.pImage_pPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:53:49.300848+00:00
-- url     : https://prove2.me/submissions/0da20d92-1b64-4532-8eee-809be122864a

module
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Theorems.Thm_UlmsTheorem_mem_pImage
attribute [local simp] UlmsTheorem.mem_pImage

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (n : ℕ) :
    pImage p (pPow p n (G := G)) = pPow p (n + 1) := by
  ext x
  simp only [mem_pImage, pPow_mem_iff]
  constructor
  · rintro ⟨y, ⟨z, hz⟩, hpy⟩
    exact ⟨z, by rw [← hpy, ← hz, pow_succ, mul_smul, smul_comm]⟩
  · rintro ⟨y, hy⟩
    exact ⟨p ^ n • y, ⟨y, rfl⟩, by rw [← hy, pow_succ, mul_smul, smul_comm]⟩
end UlmsTheorem
