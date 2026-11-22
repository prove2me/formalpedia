-- Prove2me | solution 1 for UlmsTheorem.add_zsmul_mem_iff_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:48.852507+00:00
-- url     : https://prove2.me/submissions/1299d050-163f-49aa-af9e-49d3b90ac573

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_mem_pImage
attribute [local simp] UlmsTheorem.mem_pImage


attribute [local simp] UlmsTheorem.ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution {β : Ordinal.{0}} {x c : G}
    (hx : x ∈ ulmSubgroup p β (G := G)) (n : ℤ) :
    c + n • x ∈ ulmSubgroup p β (G := G) ↔ c ∈ ulmSubgroup p β (G := G) := by
  constructor
  · intro h
    simpa using (ulmSubgroup p β (G := G)).sub_mem h
      ((ulmSubgroup p β (G := G)).zsmul_mem hx n)
  · intro h
    exact (ulmSubgroup p β (G := G)).add_mem h
      ((ulmSubgroup p β (G := G)).zsmul_mem hx n)
end UlmsTheorem
