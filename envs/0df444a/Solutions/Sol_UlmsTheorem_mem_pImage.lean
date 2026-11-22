-- Prove2me | solution 1 for UlmsTheorem.mem_pImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:53:23.920641+00:00
-- url     : https://prove2.me/submissions/90680558-3eea-4a44-9312-1b0edf9bb2df

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
theorem _root_.solution (H : AddSubgroup G) (x : G) :
    x ∈ pImage p H ↔ ∃ y ∈ H, p • y = x := Iff.rfl
end UlmsTheorem
