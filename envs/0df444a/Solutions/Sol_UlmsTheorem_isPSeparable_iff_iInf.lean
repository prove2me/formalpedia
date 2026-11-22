-- Prove2me | solution 1 for UlmsTheorem.isPSeparable_iff_iInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:49.29419+00:00
-- url     : https://prove2.me/submissions/51195559-cbc0-4b7f-8b3d-13e341e60fdd

module
public import Mathlib.Data.ENat.Lattice
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution :
    IsPSeparable p G ↔ (⨅ n : ℕ, pPow p (G := G) n) = ⊥ := by
  constructor
  · intro hred
    ext x
    simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_bot]
    exact ⟨fun h ↦ hred x (fun n ↦ (pPow_mem_iff p x n).mp (h n)),
      fun h n ↦ h ▸ (pPow p (G := G) n).zero_mem⟩
  · intro h x hx
    have hmem : x ∈ ⨅ n : ℕ, pPow p (G := G) n := by
      simp only [AddSubgroup.mem_iInf]
      intro n
      exact (pPow_mem_iff p x n).mpr (hx n)
    rw [h] at hmem
    exact AddSubgroup.mem_bot.mp hmem
end UlmsTheorem
