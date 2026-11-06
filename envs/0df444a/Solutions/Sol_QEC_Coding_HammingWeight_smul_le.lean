-- Prove2me | solution 1 for QEC.Coding.HammingWeight_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:36.96524+00:00
-- url     : https://prove2.me/submissions/8052b46d-3a30-4a0c-b6af-490c41ea1d64

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_hammingSupport_smul_subset

set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
namespace QEC.Coding
theorem _root_.solution
    {F : Type u} [Field F] [DecidableEq F]
    {ι : Type v} [Fintype ι]
    (a : F) (x : Word F ι) :
    HammingWeight (a • x) ≤ HammingWeight x := by
  exact Finset.card_le_card (hammingSupport_smul_subset a x)
end QEC.Coding
