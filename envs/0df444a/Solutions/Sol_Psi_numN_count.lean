-- Prove2me | solution 1 for Psi.numN_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:30:56.43291+00:00
-- url     : https://prove2.me/submissions/09861197-d091-4f69-bba9-47dfc04d6bad

import Definitions.Def_RequestProject_Psi_PathLemmas
import Definitions.Def_RequestProject_Psi_PhiBasic
import Theorems.Thm_Psi_numN_cons

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (le sn : Bool) :
    numN p = countRises p le sn + countValleys p le
      + (if le = false ∧ sn = false ∧ p.head? = some true then 1 else 0) := by
  induction p generalizing le sn with
  | nil => simp [numN, countRises, countValleys]
  | cons a t ih =>
      rw [numN_cons]
      cases a with
      | true =>
          rw [ih false true]
          cases le <;> cases sn <;>
            simp [countRises, countValleys] <;> omega
      | false =>
          rw [ih true sn]
          cases le <;> cases sn <;>
            simp [countRises, countValleys]
end Psi
