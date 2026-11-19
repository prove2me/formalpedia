-- Prove2me | solution 1 for QEC.Distillation.BK15.l1_dual_decomposition_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:07:46.742372+00:00
-- url     : https://prove2.me/submissions/b416aa55-2b06-4d18-b045-d2b409bfacfa

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1DualCoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution
    {b b' : Sum (Fin 4) QuadraticIndex → Bit} {c c' : Bit}
    (h : l2CoefficientMap b + c • allOnes = l2CoefficientMap b' + c' • allOnes) :
    b = b' ∧ c = c' := by
  change l1DualCoefficientMap (b, c) = l1DualCoefficientMap (b', c') at h
  have hPair : (b, c) = (b', c') := l1DualCoefficientMap_injective h
  exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
end QEC.Distillation.BK15
