-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.certificateFailureProbability_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:02:43.829171+00:00
-- url     : https://prove2.me/submissions/aec15844-f07b-4e91-ba5e-26a4dfa86a7f

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_card_nonpositiveBlock_twelve

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (blocks : Nat) :
    certificateFailureProbability 12 blocks = (4095 / 4096 : Real) ^ blocks := by
  have hBool : Fintype.card Bool = 2 := by decide +kernel
  simp only [certificateFailureProbability, Fintype.card_fun,
    Fintype.card_fin, card_nonpositiveBlock_twelve]
  rw [div_pow]
  norm_num [hBool, Nat.cast_pow]
end QEC.Distillation.PhaseRetry
