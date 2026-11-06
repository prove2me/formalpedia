-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.HammingWeight_basisCoboundary_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:23.519171+00:00
-- url     : https://prove2.me/submissions/d573f4fb-4496-421e-b962-aa277e10584f

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_primaryCheckCoboundary_le_three
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_auxiliaryCheckCoboundary_le_two

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution (q : WeightReducedCheck R) :
    HammingWeight (basisCoboundary (F := F) R q) ≤ 3 := by
  cases q with
  | inl e => exact HammingWeight_primaryCheckCoboundary_le_three (F := F) R e
  | inr a =>
      exact (HammingWeight_auxiliaryCheckCoboundary_le_two (F := F) R a).trans
        (by norm_num)
end QEC.Coding.ClassicalWeightReduction
