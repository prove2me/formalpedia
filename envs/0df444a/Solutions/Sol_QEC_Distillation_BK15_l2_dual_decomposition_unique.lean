-- Prove2me | solution 1 for QEC.Distillation.BK15.l2_dual_decomposition_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:07:50.268837+00:00
-- url     : https://prove2.me/submissions/559997e0-c4c1-4355-aba4-0ab8c382f2bb

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2DualCoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution
    {a a' : Fin 4 → Bit} {c c' : Bit}
    (h : l1CoefficientMap a + c • allOnes = l1CoefficientMap a' + c' • allOnes) :
    a = a' ∧ c = c' := by
  change l2DualCoefficientMap (a, c) = l2DualCoefficientMap (a', c') at h
  have hPair : (a, c) = (a', c') := l2DualCoefficientMap_injective h
  exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
end QEC.Distillation.BK15
