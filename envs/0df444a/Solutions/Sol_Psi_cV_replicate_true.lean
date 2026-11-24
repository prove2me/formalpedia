-- Prove2me | solution 1 for Psi.cV_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:08:08.107673+00:00
-- url     : https://prove2.me/submissions/aebf2a76-084a-4bd7-b626-b5667f640abc

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) (le : Bool) :
    countValleys (List.replicate n true) le = (if le ∧ 1 ≤ n then 1 else 0) := by
  cases n with
  | zero => simp [countValleys]
  | succ m =>
      rw [List.replicate_succ]
      have h0 : countValleys (List.replicate m true) false = 0 := by
        clear le; induction m with
        | zero => simp [countValleys]
        | succ k ih => rw [List.replicate_succ]; simpa [countValleys] using ih
      simp only [countValleys, h0]; cases le <;> simp
end Psi
