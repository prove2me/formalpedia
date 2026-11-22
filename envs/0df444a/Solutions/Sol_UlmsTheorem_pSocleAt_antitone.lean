-- Prove2me | solution 1 for UlmsTheorem.pSocleAt_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:25.478513+00:00
-- url     : https://prove2.me/submissions/df5acca6-4af7-4a5f-a97c-cb7b3ac1b5b4

module
public import Mathlib.Algebra.Module.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone


set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution : Antitone (fun α ↦ pSocleAt p α (G := G)) := fun _ _ h ↦
  inf_le_inf_left _ (ulmSubgroup_antitone p h)
end UlmsTheorem
