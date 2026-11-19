-- Prove2me | solution 1 for QEC.Distillation.BK15.mem_l1_dual_iff_exists_l2_plus_allOnes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:08:47.524211+00:00
-- url     : https://prove2.me/submissions/9264a7c1-310d-4932-b206-ecc949efbda7

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1_dual_carrier_eq_model

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (w : Word) :
    w ∈ L1.dual.carrier ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, ∃ c : Bit,
        w = l2CoefficientMap b + c • allOnes := by
  constructor
  · intro hw
    rw [l1_dual_carrier_eq_model] at hw
    rcases hw with ⟨bc, hbc⟩
    exact ⟨bc.1, bc.2, hbc.symm⟩
  · rintro ⟨b, c, rfl⟩
    rw [l1_dual_carrier_eq_model]
    exact ⟨(b, c), rfl⟩
end QEC.Distillation.BK15
