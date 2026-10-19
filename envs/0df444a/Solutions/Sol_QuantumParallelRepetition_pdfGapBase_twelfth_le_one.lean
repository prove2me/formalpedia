-- Prove2me | solution 1 for QuantumParallelRepetition.pdfGapBase_twelfth_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/d93d27a8-e9f4-4dcd-b70a-04ac18b2ee26

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapBase_twelfth_le_gap

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (unit : ε ≤ 1) :
    (ε / (4 * B)) ^ 12 ≤ 1 :=
  (pdfGapBase_twelfth_le_gap constant gap unit).trans unit
end QuantumParallelRepetition
