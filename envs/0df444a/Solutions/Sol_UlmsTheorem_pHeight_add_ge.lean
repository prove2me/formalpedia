-- Prove2me | solution 1 for UlmsTheorem.pHeight_add_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:56:58.221602+00:00
-- url     : https://prove2.me/submissions/d53a177b-7aae-4ea9-9154-38ea270e466a

module
public import Mathlib.Data.ENat.Lattice
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Theorems.Thm_UlmsTheorem_pHeight_ge_iff

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (x y : G) (n : ℕ)
    (hx : (n : ℕ∞) ≤ pHeight p x) (hy : (n : ℕ∞) ≤ pHeight p y) :
    (n : ℕ∞) ≤ pHeight p (x + y) := by
  rw [pHeight_ge_iff] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [smul_add, ha, hb]⟩
end UlmsTheorem
