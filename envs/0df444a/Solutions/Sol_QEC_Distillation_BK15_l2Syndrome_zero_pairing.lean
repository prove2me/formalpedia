-- Prove2me | solution 1 for QEC.Distillation.BK15.l2Syndrome_zero_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:07:23.719483+00:00
-- url     : https://prove2.me/submissions/8a9c4dc2-a8e9-44fa-8297-0ee0fc900ca6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_wordPairing_l2CoefficientMap

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (w : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit)
    (hzero : l2Syndrome w = 0) : wordPairing w (l2CoefficientMap b) = 0 := by
  rw [wordPairing_l2CoefficientMap]
  apply Finset.sum_eq_zero
  intro g _
  have hg := congrFun hzero g
  change wordPairing w (l2Generator g) = 0 at hg
  rw [hg, smul_zero]
end QEC.Distillation.BK15
