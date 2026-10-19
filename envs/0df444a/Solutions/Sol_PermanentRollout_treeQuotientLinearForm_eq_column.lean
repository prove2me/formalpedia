-- Prove2me | solution 1 for PermanentRollout.treeQuotientLinearForm_eq_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/71535fcf-9198-4d29-b4f2-6953da9f10bd

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r k : ℕ}
    (U : Matrix (Fin r) (Fin k) ℂ) (column : Fin k) :
    Ideal.Quotient.mk (squareZeroIdeal r) (columnLinearForm U column) =
      treeQuotientLinearForm (fun row => U row column) := by
  simp only [columnLinearForm, treeQuotientLinearForm,
    squareZeroVariable, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro row _
  congr 1
end PermanentRollout
