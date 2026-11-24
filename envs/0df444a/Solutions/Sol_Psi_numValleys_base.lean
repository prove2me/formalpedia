-- Prove2me | solution 1 for Psi.numValleys_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:32:30.397901+00:00
-- url     : https://prove2.me/submissions/e10145dd-0ab2-4687-b4ed-ece71bc3edfd

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_countValleys_append
import Theorems.Thm_Psi_cV_replicate_true
import Theorems.Thm_Psi_cV_replicate_false
import Theorems.Thm_Psi_cVstate_fUD

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l k : Nat) :
    numValleys ((List.replicate l [true, false]).flatten ++ List.replicate (k+1) true
      ++ List.replicate (k+1) false) = l := by
  unfold numValleys
  rw [show ((List.replicate l [true, false]).flatten ++ List.replicate (k+1) true
        ++ List.replicate (k+1) false) = fUD l ++ (List.replicate (k+1) true
          ++ List.replicate (k+1) false) from by unfold fUD; simp only [List.append_assoc]]
  rw [countValleys_append, countValleys_append, cV_replicate_false, add_zero, cV_replicate_true]
  simp only [show (1:Nat) ≤ k+1 from Nat.le_add_left 1 k, and_true]
  exact cVstate_fUD l
end Psi
