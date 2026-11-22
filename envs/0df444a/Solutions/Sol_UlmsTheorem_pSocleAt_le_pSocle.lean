-- Prove2me | solution 1 for UlmsTheorem.pSocleAt_le_pSocle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:31.731058+00:00
-- url     : https://prove2.me/submissions/0c5dae52-7d87-43b0-9437-2ba15a6b2de7

module
public import Mathlib.Algebra.Module.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (α : Ordinal) :
    pSocleAt p α (G := G) ≤ pSocle p :=
  inf_le_left
end UlmsTheorem
