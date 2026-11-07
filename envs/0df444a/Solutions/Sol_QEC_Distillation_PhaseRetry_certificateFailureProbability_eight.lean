-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.certificateFailureProbability_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:02:32.589091+00:00
-- url     : https://prove2.me/submissions/0242d31b-fe99-4d55-985e-b88da224f30b

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_card_nonpositiveBlock_eight

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (blocks : Nat) :
    certificateFailureProbability 8 blocks = (255 / 256 : Real) ^ blocks := by
  have hBool : Fintype.card Bool = 2 := by decide +kernel
  simp only [certificateFailureProbability, Fintype.card_fun,
    Fintype.card_fin, card_nonpositiveBlock_eight]
  rw [div_pow]
  norm_num [hBool, Nat.cast_pow]
end QEC.Distillation.PhaseRetry
