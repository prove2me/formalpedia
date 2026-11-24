-- Prove2me | solution 1 for Psi.hasDD_split_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:34:46.641937+00:00
-- url     : https://prove2.me/submissions/baa13df3-1da4-4a3f-9c2c-a6e02527899a

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_hasDD_append_false
import Theorems.Thm_Psi_hasDD_replicate_true
import Theorems.Thm_Psi_hasDD_fUD
import Theorems.Thm_Psi_hasDD_split_of_B
import Theorems.Thm_Psi_numN_append
import Theorems.Thm_Psi_numN_fUD
import Theorems.Thm_Psi_numN_replicate_true
import Theorems.Thm_Psi_stEast_append
import Theorems.Thm_Psi_stEast_replicate_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l k h : ℕ) (hh : h ≤ l + k + 1) :
    hasDD (splitAtRow ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
      ++ List.replicate (k + 1) false) h).1 = false := by
  rw [show (List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true
        ++ List.replicate (k + 1) false
      = ((List.replicate l [true, false]).flatten ++ List.replicate (k + 1) true ++ [false])
        ++ List.replicate k false from by
    rw [show List.replicate (k + 1) false = [false] ++ List.replicate k false from by
          rw [List.replicate_succ]; rfl]
    simp only [List.append_assoc]]
  apply hasDD_split_of_B
  · rw [stEast_append]; simp [stEast]
  · simp only [numN_append, numN_replicate_true,
      show numN ((List.replicate l [true, false]).flatten) = l from numN_fUD l,
      show numN [false] = 0 from rfl]
    omega
  · apply hasDD_append_false
    · apply hasDD_append_false
      · exact hasDD_fUD l
      · exact hasDD_replicate_true (k + 1)
      · intro _; rw [List.replicate_succ]; simp
    · rfl
    · intro hcontra
      rw [stEast_append, stEast_replicate_true] at hcontra
      simp at hcontra
end Psi
