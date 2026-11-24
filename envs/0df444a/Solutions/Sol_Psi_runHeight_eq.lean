-- Prove2me | solution 1 for Psi.runHeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:29:54.055218+00:00
-- url     : https://prove2.me/submissions/655b69e3-0012-4775-8927-7a2be0666bee

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_numE_cons_true
import Theorems.Thm_Psi_numE_cons_false
import Theorems.Thm_Psi_numN_cons_true
import Theorems.Thm_Psi_numN_cons_false

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : Int) :
    runHeight p h = h + numN p - numE p := by
  induction p generalizing h with
  | nil => simp [runHeight, numN, numE]
  | cons a t ih =>
    cases a with
    | true => rw [numN_cons_true, numE_cons_true]; simp only [runHeight]; rw [ih]; push_cast; ring
    | false => rw [numN_cons_false, numE_cons_false]; simp only [runHeight]; rw [ih]; push_cast; ring
end Psi
