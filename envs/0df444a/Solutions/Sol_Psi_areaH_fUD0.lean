-- Prove2me | solution 1 for Psi.areaH_fUD0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:10:23.638877+00:00
-- url     : https://prove2.me/submissions/aa048213-435a-4823-9a70-7a5c8e4197dc

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_areaH_append

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Nat) (le : Bool) : areaH (fUD a) 0 le = 0 := by
  induction a generalizing le with
  | zero => simp [fUD, areaH]
  | succ m ih =>
    unfold fUD; rw [List.replicate_succ, List.flatten_cons, areaH_append]
    have h1 : areaH [true, false] 0 le = 0 := by cases le <;> simp [areaH]
    have hr : runHeight [true, false] 0 = 0 := by simp [runHeight]
    rw [h1, hr]; simpa [fUD] using ih (stEast [true, false] le)
end Psi
