-- Prove2me | solution 1 for UlmsTheorem.pSocleAt_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:44.881644+00:00
-- url     : https://prove2.me/submissions/dd40b0d3-80aa-4fb6-b4e7-e53ae02d3030

module
public import Mathlib.Algebra.Module.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Theorems.Thm_UlmsTheorem_pSocleAt_antitone

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (α : Ordinal) :
    pSocleAt p (Order.succ α) (G := G) ≤ pSocleAt p α :=
  pSocleAt_antitone p (Order.le_succ α)
end UlmsTheorem
