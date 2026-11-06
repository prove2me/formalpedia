-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.HammingWeight_auxiliaryCheckCoboundary_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:46.005087+00:00
-- url     : https://prove2.me/submissions/f971e608-5d1c-4b76-bbc6-5efe9345b577

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_single_le_one
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


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
theorem _root_.solution (a : AuxiliaryCheck R) :
    HammingWeight (auxiliaryCheckCoboundary (F := F) R a) ≤ 2 := by
  unfold auxiliaryCheckCoboundary
  exact (HammingWeight_add_le _ _).trans
    (Nat.add_le_add
      (HammingWeight_single_le_one (F := F) _)
      (HammingWeight_single_le_one (F := F) _))
end QEC.Coding.ClassicalWeightReduction
