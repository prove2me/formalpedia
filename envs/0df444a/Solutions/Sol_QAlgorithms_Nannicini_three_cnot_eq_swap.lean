-- Prove2me | solution 1 for QAlgorithms.Nannicini.three_cnot_eq_swap
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-17T21:18:31.861126+00:00
-- url     : https://prove2.me/submissions/18532ce4-c740-4821-ab70-a8b336d23a06

import Definitions.Def_QAlgorithms_Defs_Gates

set_option autoImplicit false
open QAlgorithms

theorem solution :
    cnot * cnot.submatrix Prod.swap Prod.swap * cnot = swapGate := by
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, cnot, swapGate, Matrix.submatrix_apply]
