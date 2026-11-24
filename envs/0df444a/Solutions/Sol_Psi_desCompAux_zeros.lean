-- Prove2me | solution 1 for Psi.desCompAux_zeros
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:32:57.600797+00:00
-- url     : https://prove2.me/submissions/30724ed2-54ae-4072-8451-e36e178bf799

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : ℕ) (rest : List Bool) (cur : ℕ) :
    desCompAux (List.replicate a false ++ (true :: rest)) cur
      = desCompAux (true :: rest) (cur + a) := by
  induction a generalizing cur with
  | zero => simp
  | succ m ih =>
    have hstart : List.replicate (m+1) false ++ (true :: rest)
        = false :: (List.replicate m false ++ (true :: rest)) := by
          rw [List.replicate_succ, List.cons_append]
    rw [hstart]
    cases hm : List.replicate m false ++ (true :: rest) with
    | nil => simp at hm
    | cons y ys =>
      simp only [desCompAux, Bool.false_and, if_false, Bool.false_eq_true]
      rw [← hm, ih]; congr 1; omega
end Psi
