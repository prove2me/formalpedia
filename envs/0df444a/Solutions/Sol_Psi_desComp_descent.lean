-- Prove2me | solution 1 for Psi.desComp_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:35:11.6898+00:00
-- url     : https://prove2.me/submissions/863fcca8-b36e-4532-a04a-f3f3fd8062e7

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_desCompAux_zeros
import Theorems.Thm_Psi_desCompAux_ones
import Theorems.Thm_Psi_noDescent_false_decomp


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution {w : List Bool} (hnd : noDescent w = false) :
    desComp (false :: w)
      = (cLead0 w + 1 + cLead1 (w.drop (cLead0 w)))
        :: desComp (false :: (w.drop (cLead0 w)).drop (cLead1 (w.drop (cLead0 w)) + 1)) := by
  obtain ⟨hdec, hb⟩ := noDescent_false_decomp hnd
  set a := cLead0 w
  set b := cLead1 (w.drop a)
  set w' := (w.drop a).drop (b+1)
  clear_value w' b a
  conv_lhs => rw [hdec]
  have hre : false :: (List.replicate a false ++ List.replicate b true ++ false :: w')
      = List.replicate (a+1) false ++ (List.replicate b true ++ (false :: w')) := by
    rw [List.replicate_succ]; simp [List.append_assoc]
  rw [hre]
  have hstart : List.replicate b true ++ (false :: w')
      = true :: (List.replicate (b-1) true ++ (false :: w')) := by
    cases b with | zero => omega | succ m => rw [List.replicate_succ, List.cons_append]; simp
  unfold desComp
  rw [hstart, desCompAux_zeros, ← hstart, desCompAux_ones b hb]
  congr 1; omega
end Psi
