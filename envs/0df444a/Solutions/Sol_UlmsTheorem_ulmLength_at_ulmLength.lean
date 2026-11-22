-- Prove2me | solution 1 for UlmsTheorem.ulmLength.at_ulmLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:34.870198+00:00
-- url     : https://prove2.me/submissions/aa40cd0a-8423-4b15-b2a5-7c8082c9f6a3

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Theorems.Thm_UlmsTheorem_ulmLength_exists_zero

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
theorem _root_.solution (hred : IsPReduced p G) :
    ulmSubgroup p (ulmLength p (G := G)) (G := G) = ⊥ :=
  csInf_mem (exists_zero (p := p) (G := G) hred)
end UlmsTheorem.ulmLength
