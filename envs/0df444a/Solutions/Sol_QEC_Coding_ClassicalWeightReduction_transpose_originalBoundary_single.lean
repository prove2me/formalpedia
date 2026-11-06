-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.transpose_originalBoundary_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:57.3852+00:00
-- url     : https://prove2.me/submissions/f0c863b8-4587-4465-b8dc-8d7d7876710a

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_wordLinearMapTranspose_linearMapOfBasisImages_single

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [DecidableEq F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution (c : Check) :
    wordLinearMapTranspose (originalBoundary (F := F) R) (Pi.single c 1) =
      fun b => if R c b then 1 else 0 := by
  unfold originalBoundary
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  rfl
end QEC.Coding.ClassicalWeightReduction
