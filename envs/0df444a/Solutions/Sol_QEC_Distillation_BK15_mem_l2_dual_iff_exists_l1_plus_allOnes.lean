-- Prove2me | solution 1 for QEC.Distillation.BK15.mem_l2_dual_iff_exists_l1_plus_allOnes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:08:23.927872+00:00
-- url     : https://prove2.me/submissions/ed28799d-2501-4e51-876e-fc363ca3660e

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2_dual_carrier_eq_model

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (w : Word) :
    w ∈ L2.dual.carrier ↔
      ∃ a : Fin 4 → Bit, ∃ c : Bit,
        w = l1CoefficientMap a + c • allOnes := by
  constructor
  · intro hw
    rw [l2_dual_carrier_eq_model] at hw
    rcases hw with ⟨ac, hac⟩
    exact ⟨ac.1, ac.2, hac.symm⟩
  · rintro ⟨a, c, rfl⟩
    rw [l2_dual_carrier_eq_model]
    exact ⟨(a, c), rfl⟩
end QEC.Distillation.BK15
