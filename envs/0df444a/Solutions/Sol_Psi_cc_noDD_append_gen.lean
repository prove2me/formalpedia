-- Prove2me | solution 1 for Psi.cc_noDD_append_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:12:37.207009+00:00
-- url     : https://prove2.me/submissions/e81dfaf4-52de-47d2-a2e0-515c48412bd0

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rho Z : List Bool) (hrho : hasDD rho = false) :
    cc (rho ++ Z)
      = List.replicate (numN rho) true ++ (if stEast rho false then cc (false :: Z) else cc Z) := by
  induction rho with
  | nil => simp [numN, stEast]
  | cons a r ih =>
    cases a with
    | true =>
      have hr : hasDD r = false := by simpa [hasDD] using hrho
      have hnn : numN (true :: r) = numN r + 1 := by simp [numN]
      have hse : stEast (true :: r) false = stEast r false := by simp [stEast]
      rw [List.cons_append, cc, ih hr, hnn, hse, List.replicate_succ, List.cons_append]
    | false =>
      cases r with
      | nil =>
        have hnn : numN ([false] : List Bool) = 0 := by simp [numN]
        have hse : stEast ([false] : List Bool) false = true := by simp [stEast]
        rw [hnn, hse]
        simp only [List.replicate_zero, List.nil_append, if_true]
        rw [List.singleton_append]
      | cons b r' =>
        cases b with
        | false => simp [hasDD] at hrho
        | true =>
          have hr : hasDD (true :: r') = false := by simpa [hasDD] using hrho
          have hnn : numN (false :: true :: r') = numN (true :: r') := by
            simp [numN]
          have hse : stEast (false :: true :: r') false = stEast (true :: r') false := by
            simp [stEast]
          have hcc : cc (false :: true :: r' ++ Z) = cc ((true :: r') ++ Z) := rfl
          rw [hcc, hnn, hse, ih hr]
end Psi
