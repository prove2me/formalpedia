-- Prove2me | solution 1 for Psi.trail_true_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:45:55.438287+00:00
-- url     : https://prove2.me/submissions/d0be70bf-769a-4fa6-8d16-715d5ceff961

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_dropWhile_eq_drop
import Theorems.Thm_Psi_head_dropWhile_id
import Theorems.Thm_Psi_lead_true_split

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (A : List Bool) :
    A = A.take (A.length - (A.reverse.takeWhile id).length)
          ++ List.replicate ((A.reverse.takeWhile id).length) true
      ∧ (A.take (A.length - (A.reverse.takeWhile id).length)).getLast? ≠ some true := by
  set p := (A.reverse.takeWhile id).length with hp
  have hrev : A.reverse = List.replicate p true ++ A.reverse.dropWhile id := lead_true_split A.reverse
  have hdw : A.reverse.dropWhile id = A.reverse.drop p := by rw [dropWhile_eq_drop, hp]
  have hAeq : A = (A.reverse.drop p).reverse ++ List.replicate p true := by
    have := congrArg List.reverse hrev
    rw [List.reverse_reverse, List.reverse_append, List.reverse_replicate, hdw] at this
    exact this
  have hdrev : (A.reverse.drop p).reverse = A.take (A.length - p) := by
    rw [List.reverse_drop, List.reverse_reverse, List.length_reverse]
  refine ⟨by rw [hdrev] at hAeq; exact hAeq, ?_⟩
  rw [hdrev] at hAeq
  have : (A.take (A.length - p)).getLast? = (A.reverse.drop p).head? := by
    rw [← hdrev, List.getLast?_reverse]
  rw [this, ← hdw]; exact head_dropWhile_id _
end Psi
