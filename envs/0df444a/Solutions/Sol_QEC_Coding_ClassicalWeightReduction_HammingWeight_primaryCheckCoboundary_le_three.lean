-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.HammingWeight_primaryCheckCoboundary_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:42.736488+00:00
-- url     : https://prove2.me/submissions/12bb3771-4f78-42b8-a8e4-d208ca9be57f

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_single_le_one
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_optionalSingle_le_one
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
theorem _root_.solution (e : Incidence R) :
    HammingWeight (primaryCheckCoboundary (F := F) R e) ≤ 3 := by
  calc
    HammingWeight (primaryCheckCoboundary (F := F) R e) ≤
        HammingWeight (Pi.single (Sum.inl e) (1 : F) :
          Word F (WeightReducedBit R)) +
          HammingWeight (optionalSingle (F := F)
            ((pathPrevious (checkPosition R e)).map
              (auxiliaryBitIndex R e.1.1))) +
          HammingWeight (optionalSingle (F := F)
            ((pathNext (checkPosition R e)).map
              (auxiliaryBitIndex R e.1.1))) := by
      unfold primaryCheckCoboundary
      exact (HammingWeight_add_le _ _).trans
        (Nat.add_le_add_right (HammingWeight_add_le _ _) _)
    _ ≤ 1 + 1 + 1 := by
      gcongr
      · exact HammingWeight_single_le_one (F := F) _
      · exact HammingWeight_optionalSingle_le_one (F := F) _
      · exact HammingWeight_optionalSingle_le_one (F := F) _
    _ = 3 := by norm_num
end QEC.Coding.ClassicalWeightReduction
