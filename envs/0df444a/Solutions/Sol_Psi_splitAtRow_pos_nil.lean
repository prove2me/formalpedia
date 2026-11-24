-- Prove2me | solution 1 for Psi.splitAtRow_pos_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:27:38.687566+00:00
-- url     : https://prove2.me/submissions/4dd6dd54-6220-47f0-91b8-36d5d8050550

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : Nat) :
    (splitAtRow p (h+1)).1 = [] → splitAtRow p (h+1) = ([], []) := by
  cases p with
  | nil => intro _; simp [splitAtRow]
  | cons a rest =>
      cases a with
      | true =>
          cases h with
          | zero => intro hh; simp only [splitAtRow] at hh ⊢; split at hh <;> simp_all
          | succ h => intro hh; simp only [splitAtRow] at hh; exact (List.cons_ne_nil _ _ hh).elim
      | false => intro hh; simp only [splitAtRow] at hh; exact (List.cons_ne_nil _ _ hh).elim
end Psi
