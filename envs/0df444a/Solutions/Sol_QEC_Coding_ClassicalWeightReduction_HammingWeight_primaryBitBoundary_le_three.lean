-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.HammingWeight_primaryBitBoundary_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:38.967036+00:00
-- url     : https://prove2.me/submissions/aa751259-cc4a-4107-9e19-2fb79795fbe5

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
    HammingWeight (primaryBitBoundary (F := F) R e) ≤ 3 := by
  calc
    HammingWeight (primaryBitBoundary (F := F) R e) ≤
        HammingWeight (Pi.single (Sum.inl e) (1 : F) :
          Word F (WeightReducedCheck R)) +
          HammingWeight (optionalSingle (F := F)
            ((pathPrevious (bitPosition R e)).map
              (auxiliaryCheckIndex R e.1.2))) +
          HammingWeight (optionalSingle (F := F)
            ((pathNext (bitPosition R e)).map
              (auxiliaryCheckIndex R e.1.2))) := by
      unfold primaryBitBoundary
      exact (HammingWeight_add_le _ _).trans
        (Nat.add_le_add_right (HammingWeight_add_le _ _) _)
    _ ≤ 1 + 1 + 1 := by
      gcongr
      · exact HammingWeight_single_le_one (F := F) _
      · exact HammingWeight_optionalSingle_le_one (F := F) _
      · exact HammingWeight_optionalSingle_le_one (F := F) _
    _ = 3 := by norm_num
end QEC.Coding.ClassicalWeightReduction
