-- Prove2me | solution 1 for Psi.desCompAux_ones
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:33:39.936077+00:00
-- url     : https://prove2.me/submissions/ce14acb2-5add-40f2-a6fe-9a7da4bb66ee

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (b : ℕ) (hb : 1 ≤ b) (rest : List Bool) (cur : ℕ) :
    desCompAux (List.replicate b true ++ (false :: rest)) cur
      = (cur + b) :: desCompAux (false :: rest) 0 := by
  induction b generalizing cur with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp [desCompAux]
    | succ k =>
      have hstart : List.replicate (k+1+1) true ++ (false :: rest)
          = true :: true :: (List.replicate k true ++ (false :: rest)) := by
        rw [List.replicate_succ, List.replicate_succ, List.cons_append, List.cons_append]
      rw [hstart]
      simp only [desCompAux, Bool.and_false, Bool.not_true, if_false, Bool.false_eq_true]
      have hback : true :: (List.replicate k true ++ (false :: rest))
          = List.replicate (k+1) true ++ (false :: rest) := by
            rw [List.replicate_succ, List.cons_append]
      rw [hback, ih (by omega) (cur+1)]; congr 1; omega
end Psi
