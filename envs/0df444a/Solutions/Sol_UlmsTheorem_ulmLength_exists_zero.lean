-- Prove2me | solution 1 for UlmsTheorem.ulmLength.exists_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:51.952034+00:00
-- url     : https://prove2.me/submissions/69c03f38-5bee-44ad-a01c-d3d2a4ea498a

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal Cardinal
variable (p : ℕ) [hp : Fact p.Prime]
open UlmsTheorem.ulmLength
variable {G : Type*} [AddCommGroup G]
omit hp
namespace UlmsTheorem.ulmLength
theorem _root_.solution (hred' : IsPReduced p G) :
    ∃ α : Ordinal.{0}, ulmSubgroup p α (G := G) = ⊥ := by
  exact hred'
end UlmsTheorem.ulmLength
