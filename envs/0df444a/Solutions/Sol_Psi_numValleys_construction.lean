-- Prove2me | solution 1 for Psi.numValleys_construction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:32:12.93234+00:00
-- url     : https://prove2.me/submissions/0d3b6058-5bf0-4aa5-9336-5dcc19a40e76

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_countValleys_append
import Theorems.Thm_Psi_cV_replicate_true
import Theorems.Thm_Psi_cV_replicate_false
import Theorems.Thm_Psi_stEast_replicate_true
import Theorems.Thm_Psi_stEast_replicate_false
import Theorems.Thm_Psi_cVstate_fUD
import Theorems.Thm_Psi_cV_true_false_head

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : Nat) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hbd : stEast rho false = false → rho'.head? = some true) :
    numValleys (fUD a ++ [true] ++ rho ++ List.replicate b true
        ++ List.replicate (b+1) false ++ rho')
      = a + 1 + numValleys (rho ++ rho') := by
  unfold numValleys
  rw [show (fUD a ++ [true] ++ rho ++ List.replicate b true ++ List.replicate (b+1) false ++ rho')
        = fUD a ++ ([true] ++ (rho ++ (List.replicate b true
            ++ (List.replicate (b+1) false ++ rho')))) from by simp only [List.append_assoc]]
  rw [countValleys_append, countValleys_append, countValleys_append, countValleys_append,
    countValleys_append]
  rw [show stEast [true] (stEast (fUD a) false) = false from rfl]
  rw [show stEast (List.replicate b true) (stEast rho false) = false from by
        rw [stEast_replicate_true]; simp [hb]]
  rw [show stEast (List.replicate (b+1) false) false = true from by
        rw [stEast_replicate_false]; simp]
  rw [cV_replicate_false]
  rw [show countValleys [true] (stEast (fUD a) false)
        = (if stEast (fUD a) false then 1 else 0) from by
        cases stEast (fUD a) false <;> simp [countValleys]]
  rw [show countValleys (List.replicate b true) (stEast rho false)
        = (if stEast rho false then 1 else 0) from by rw [cV_replicate_true]; simp [hb]]
  rw [countValleys_append rho rho' false]
  have hfud := cVstate_fUD a
  by_cases hsr : stEast rho false = true
  · rw [hsr]; simp only [if_true]; omega
  · have hsrf : stEast rho false = false := Bool.not_eq_true _ |>.mp hsr
    have hcvh := cV_true_false_head rho' (hbd hsrf)
    rw [hsrf]; simp only [Bool.false_eq_true, if_false]; omega
end Psi
