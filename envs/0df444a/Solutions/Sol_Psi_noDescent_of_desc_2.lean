-- Prove2me | solution 2 for Psi.noDescent_of_desc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:48:02.139878+00:00
-- url     : https://prove2.me/submissions/696d2c0f-f2b4-4a61-9682-a0b6a3b4d09a

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_noDescent_cc

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (s t : List Bool) : noDescent (s ++ true :: false :: t) = false := by
  induction s with
  | nil => rw [List.nil_append, noDescent_cc]; simp
  | cons x s' ih =>
      cases s' with
      | nil => rw [List.nil_append] at ih; show noDescent (x :: true :: false :: t) = false
               rw [noDescent_cc, ih]; simp
      | cons y s'' => show noDescent (x :: y :: (s'' ++ true :: false :: t)) = false
                      rw [noDescent_cc]
                      show ((!x || y) && noDescent (y :: s'' ++ true :: false :: t)) = false
                      rw [ih]; simp
end Psi
