-- Prove2me | solution 1 for Psi.area_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:33:42.308559+00:00
-- url     : https://prove2.me/submissions/1924fed6-07bf-4659-baca-a5e02b79d16f

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_runHeight_eq
import Theorems.Thm_Psi_areaH_append
import Theorems.Thm_Psi_areaH_shift
import Theorems.Thm_Psi_areaH_replicate_false
import Theorems.Thm_Psi_areaH_replicate_true
import Theorems.Thm_Psi_areaH_fUD0
import Theorems.Thm_Psi_noDD_numE
import Theorems.Thm_Psi_areaH_le_diff
import Theorems.Thm_Psi_runHeight_flatten_UD
import Theorems.Thm_Psi_runHeight_replicate_false
import Theorems.Thm_Psi_runHeight_replicate_true
import Theorems.Thm_Psi_runHeight_shift
import Theorems.Thm_Psi_stEast_replicate_false
import Theorems.Thm_Psi_stEast_replicate_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) (rho rho' : List Bool) (hb : 1 ≤ b)
    (hnoDD : hasDD rho = false)
    (hbd : stEast rho false = false → rho'.head? = some true) :
    areaH ((List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') 0 false
      = (numN rho : Int) + areaH (rho ++ rho') 0 false := by
  have hexp : areaH ((List.replicate a [true, false]).flatten ++ [true] ++ rho
        ++ List.replicate b true ++ List.replicate (b + 1) false ++ rho') 0 false
      = areaH rho 1 false + (if stEast rho false then 1 + runHeight rho 0 else 0)
        + areaH rho' (runHeight rho 0) true := by
    rw [show (List.replicate a [true, false]).flatten ++ [true] ++ rho ++ List.replicate b true
          ++ List.replicate (b + 1) false ++ rho'
        = (List.replicate a [true, false]).flatten ++ ([true] ++ (rho ++ (List.replicate b true
          ++ (List.replicate (b + 1) false ++ rho')))) from by simp only [List.append_assoc]]
    rw [areaH_append, show areaH ((List.replicate a [true, false]).flatten) 0 false = 0
          from areaH_fUD0 a false,
        show runHeight ((List.replicate a [true, false]).flatten) 0 = 0
          from runHeight_flatten_UD a 0, zero_add]
    rw [areaH_append,
        show areaH [true] 0 (stEast ((List.replicate a [true, false]).flatten) false) = 0
          from by cases stEast ((List.replicate a [true, false]).flatten) false <;> simp [areaH],
        show runHeight [true] 0 = 1 from by simp [runHeight],
        show stEast [true] (stEast ((List.replicate a [true, false]).flatten) false) = false
          from rfl, zero_add]
    rw [areaH_append,
        show runHeight rho 1 = 1 + runHeight rho 0 from by
          rw [add_comm]; exact runHeight_shift rho 0 1]
    rw [areaH_append, areaH_replicate_true,
        show runHeight (List.replicate b true) (1 + runHeight rho 0)
          = (1 + runHeight rho 0) + b from runHeight_replicate_true b _,
        show stEast (List.replicate b true) (stEast rho false) = false from by
          rw [stEast_replicate_true]; simp [hb]]
    rw [areaH_append, areaH_replicate_false, zero_add,
        show runHeight (List.replicate (b + 1) false) ((1 + runHeight rho 0) + b) = runHeight rho 0
          from by rw [runHeight_replicate_false]; push_cast; ring,
        show stEast (List.replicate (b + 1) false) false = true from by
          rw [stEast_replicate_false]; simp]
    simp only [hb, and_true]
    ring
  rw [hexp]
  rw [show areaH rho 1 false = areaH rho 0 false + 1 * (countValleys rho false : Int) from by
        have h := areaH_shift rho 0 1 false; simpa using h]
  rw [areaH_append]
  have hnumE := noDD_numE rho hnoDD
  have hrh : runHeight rho 0 = (numN rho : Int) - numE rho := by rw [runHeight_eq]; ring
  have hdiff := areaH_le_diff rho' (runHeight rho 0)
  have hnv : (countValleys rho false : Int) = (numValleys rho : Int) := by rfl
  cases hle : stEast rho false with
  | true =>
    simp only [hle, if_true] at *
    have : (numE rho : Int) = numValleys rho + 1 := by exact_mod_cast hnumE
    push_cast at hrh this ⊢
    linarith [hrh, this]
  | false =>
    have hhead := hbd hle
    rw [hhead] at hdiff
    simp only [hle, Bool.false_eq_true, if_false] at *
    have : (numE rho : Int) = numValleys rho := by exact_mod_cast hnumE
    push_cast at hrh this hdiff ⊢
    linarith [hrh, this, hdiff]
end Psi
