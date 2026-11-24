-- Prove2me | solution 1 for Psi.noDescent_true_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:42:11.001437+00:00
-- url     : https://prove2.me/submissions/0a382320-6863-45e0-8cf7-7cf8dee57ad1

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (w : List Bool) (h : noDescent w = true) :
    w = List.replicate (w.filter (· = false)).length false
          ++ List.replicate (w.filter id).length true := by
  induction w with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => cases a <;> simp [List.filter]
      | cons b rest =>
          rw [noDescent] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨hab, hnd⟩ := h
          have iht := ih hnd
          cases a with
          | false =>
              conv_lhs => rw [iht]
              simp [List.filter_cons, List.replicate_succ]
          | true =>
              simp only [Bool.not_true, Bool.false_or] at hab
              subst hab
              have hnf' : (List.filter (· = false) (true :: rest)).length = 0 := by
                by_contra hc
                obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hc
                rw [hn, List.replicate_succ] at iht
                simp at iht
              have iht2 : true :: rest
                  = List.replicate (List.filter id (true :: rest)).length true := by
                conv_lhs => rw [iht]
                rw [hnf']; simp
              have hnfw : (List.filter (· = false) (true :: true :: rest)).length = 0 := by
                rw [List.filter_cons]; simpa using hnf'
              have hntw : (List.filter id (true :: true :: rest)).length
                  = (List.filter id (true :: rest)).length + 1 := by
                rw [List.filter_cons]; simp
              rw [hnfw, hntw]
              simp only [List.replicate_zero, List.nil_append, List.replicate_succ]
              rw [← iht2]
end Psi
