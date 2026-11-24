-- Prove2me | solution 1 for Psi.northRunsAux_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:39:00.806994+00:00
-- url     : https://prove2.me/submissions/af987b03-a8b4-46c4-a5df-c26837d9f762

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp
import Theorems.Thm_Psi_northRunsAux_split
import Theorems.Thm_Psi_northRunsAux_pos

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (J : List Bool) (hpt : ℕ) :
    northRunsAux J 0
      = ppart ((northRunsAux J hpt).headD 0 - hpt) ++ (northRunsAux J hpt).tail := by
  rw [northRunsAux_split J 0, northRunsAux_split J hpt]
  rcases Nat.eq_zero_or_pos (hpt + leadN J) with h0 | hpos
  · have hh : hpt = 0 := by omega
    have hl : leadN J = 0 := by omega
    subst hh
    rw [hl]
    simp only [Nat.zero_add, ppart, Nat.lt_irrefl, if_false, List.nil_append, Nat.sub_zero]
    cases hBc : northRuns (afterLeadRun J) with
    | nil => simp
    | cons bb bs =>
      have hbpos : 0 < bb := by
        have hmem : bb ∈ northRuns (afterLeadRun J) := by rw [hBc]; simp
        exact northRunsAux_pos (afterLeadRun J) 0 bb hmem
      simp [hbpos]
  · have hpp : ppart (hpt + leadN J) = [hpt + leadN J] := by simp only [ppart, hpos, if_true]
    rw [hpp]
    simp only [List.headD_cons, List.cons_append, List.tail_cons]
    rw [show hpt + leadN J - hpt = leadN J from by omega, Nat.zero_add, List.nil_append]
end Psi
