-- Prove2me | solution 1 for QEC.Coding.FiberBundle.card_le_twice_hammingWeight_binaryComplement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:56:58.680198+00:00
-- url     : https://prove2.me/submissions/171f9aab-619d-4862-9cf1-c12e5dfad652

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_add_hammingWeight_binaryComplement

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {ι : Type u} [Fintype ι] (x : Word (ZMod 2) ι)
    (hx : 2 * HammingWeight x ≤ Fintype.card ι) :
    Fintype.card ι ≤ 2 * HammingWeight (binaryComplement x) := by
  have hpartition := hammingWeight_add_hammingWeight_binaryComplement x
  omega
end QEC.Coding.FiberBundle
