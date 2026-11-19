-- Prove2me | solution 1 for QEC.Distillation.BK15.l1Syndrome_zero_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:07:20.393807+00:00
-- url     : https://prove2.me/submissions/e8b57ba5-8c44-4143-a28a-9c72534abdd2

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_wordPairing_l1CoefficientMap

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (w : Word) (a : Fin 4 → Bit)
    (hzero : l1Syndrome w = 0) : wordPairing w (l1CoefficientMap a) = 0 := by
  rw [wordPairing_l1CoefficientMap]
  apply Finset.sum_eq_zero
  intro j _
  have hj := congrFun hzero j
  change wordPairing w (linearGenerator j) = 0 at hj
  rw [hj, smul_zero]
end QEC.Distillation.BK15
