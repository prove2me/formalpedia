-- Prove2me | solution 1 for QEC.Distillation.BK15.mem_l2DualWords_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:10:19.922476+00:00
-- url     : https://prove2.me/submissions/746718bd-5276-4265-a0e2-37a3492968c9

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2_dual_carrier_eq_model

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (w : Word) : w ∈ l2DualWords ↔ w ∈ L2.dual.carrier := by
  constructor
  · intro hw
    rw [l2DualWords, Finset.mem_image] at hw
    rcases hw with ⟨ac, -, hac⟩
    rw [l2_dual_carrier_eq_model]
    exact ⟨ac, hac⟩
  · intro hw
    rw [l2_dual_carrier_eq_model] at hw
    rcases hw with ⟨ac, hac⟩
    rw [l2DualWords, Finset.mem_image]
    exact ⟨ac, Finset.mem_univ _, hac⟩
end QEC.Distillation.BK15
