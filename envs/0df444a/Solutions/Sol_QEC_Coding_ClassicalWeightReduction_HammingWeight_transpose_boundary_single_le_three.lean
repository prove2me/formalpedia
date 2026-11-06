-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.HammingWeight_transpose_boundary_single_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:50:17.987133+00:00
-- url     : https://prove2.me/submissions/637ca30e-076d-4db7-bd79-9a2220e200be

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_basisCoboundary_le_three

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    (q : WeightReducedCheck R) :
    HammingWeight
      (wordLinearMapTranspose (boundary (F := F) R) (Pi.single q 1)) ≤ 3 := by
  rw [transpose_boundary_single]
  exact HammingWeight_basisCoboundary_le_three (F := F) R q
end QEC.Coding.ClassicalWeightReduction
