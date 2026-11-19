-- Prove2me | solution 1 for QEC.Distillation.BK15.mem_l1DualWords_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:10:16.616612+00:00
-- url     : https://prove2.me/submissions/8a5b8d71-d7ed-415a-83f0-2de359c0df65

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1_dual_carrier_eq_model

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
set_option maxRecDepth 16384
namespace QEC.Distillation.BK15
theorem _root_.solution (w : Word) : w ∈ l1DualWords ↔ w ∈ L1.dual.carrier := by
  constructor
  · intro hw
    rw [l1DualWords, Finset.mem_image] at hw
    rcases hw with ⟨bc, -, hbc⟩
    rw [l1_dual_carrier_eq_model]
    exact ⟨bc, hbc⟩
  · intro hw
    rw [l1_dual_carrier_eq_model] at hw
    rcases hw with ⟨bc, hbc⟩
    rw [l1DualWords, Finset.mem_image]
    exact ⟨bc, Finset.mem_univ _, hbc⟩
end QEC.Distillation.BK15
