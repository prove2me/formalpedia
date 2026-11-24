-- Prove2me | solution 1 for Psi.areaH_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:10:15.496257+00:00
-- url     : https://prove2.me/submissions/e142018a-1c1c-4326-9ef5-03745a31b804

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) (ht : Int) (le : Bool) :
    areaH (List.replicate n false) ht le = 0 := by
  induction n generalizing ht le with
  | zero => simp [areaH]
  | succ m ih => rw [List.replicate_succ]; simp only [areaH]; rw [ih]
end Psi
